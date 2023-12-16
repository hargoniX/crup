import Lean.Data.Parsec
import Lean.Data.PersistentHashSet
import Lean.Data.HashSet
open Lean Parsec

/--
Pop an element from a `Lean.PersistentHashSet`, this function is sadly not implemented in core (yet).
-/
def Lean.PersistentHashSet.pop! [BEq α] [Hashable α] [Inhabited α] (set : PersistentHashSet α) : α :=
  -- There is sadly no pop so we do a little hack. The idea here is that we only ever call this function
  -- on singleton sets anyways so it doesn't matter that we iterate over the entire set with fold
  set.fold (init := none) (fun _ lit => some lit) |>.get!

-- We use a PersistentHashSet of clauses because we often remove items during unit propagation
-- but want to keep the original around for later use.
-- Instead of writing a cooler unit propagation algo we rely on persistent datastructures
-- to give us at least some performance boost.
abbrev Clause := PersistentHashSet Int
-- Since we frequently add and remove elements to the list of clauses this is a List and not an Array
abbrev Clauses := List Clause
-- The unit clauses only get added to and we don't care about previous versions -> no persistent hashset.
abbrev UnitClauses := List Int


def Clause.toList (c : Clause) : List Int := c.set.toList.map Prod.fst
def Clauses.toList (cs : Clauses) : List (List Int) := cs.map Clause.toList

def parseLit : Parsec Int := do
  let c ← peek!
  let factor ←
    if c == '-' then
      skip
      pure (-1)
    else
      pure 1
  -- Could be made much more efficient
  let digits ← many1 digit
  let digitString := String.mk digits.toList
  let number := String.toNat! digitString
  return number * factor

partial def parseClause : Parsec Clause := do
  go {}
where
  go (clause : PersistentHashSet Int) : Parsec Clause := do
    let nextLit ← parseLit
    if nextLit == 0 then
      ws
      return clause
    else
      ws
      go (clause.insert nextLit)

def parseClauses : Parsec Clauses := do
  let clauses ← many parseClause
  return clauses.toList

def parseDimacs : Parsec Clauses := do
  -- Skip the header line
  skipString "p"
  ws
  skipString "cnf"
  ws
  let _vars ← many1 digit
  ws
  let _clauses ← many1 digit
  ws
  let ret ← parseClauses
  eof
  return ret

def parseRup : Parsec Clauses := do
  -- Skip the header line
  skipString "%RUPD32"
  ws
  let _vars ← many1 digit
  ws
  let _clauses ← many1 digit
  ws
  let ret ← parseClauses
  eof
  return ret

structure LogCfg where
  indent : Nat
  active : Bool

abbrev LogM (α) := ReaderT LogCfg IO α

@[inline]
def withAdditionalIndent (additional : Nat) (x : LogM α) : LogM α :=
  withReader (fun cfg => { cfg with indent := cfg.indent + additional }) x

@[inline]
def log (x : String) : LogM Unit := do
  let cfg ← read
  if cfg.active then
    let level := cfg.indent
    let pref := level.fold (init := "") (fun _ s => s.push ' ')
    IO.println s!"{pref}{x}"

structure RupState where
  known : Clauses
  todo : Clauses
deriving Inhabited

/--
The three kinds of RUP results.
-/
inductive RupResult where
/--
The proof we were told to carry out was a success.
-/
| success
/--
We got stuck while attempting to prove a RUP goal.
-/
| stuck
/--
This only occurs when we want to prove UNSAT using RUP and fail so in the last step.
-/
| failure
deriving Inhabited

/--
Compute the negation of a `Clause` as a list of `UnitClauses`.
-/
def Clause.negation (c : Clause) : UnitClauses :=
  c.fold (init := []) (fun cs lit => (-lit) :: cs)

/--
Split a list of `Clauses` into `UnitClauses` and non unit `Clauses`.
-/
def partitionUnitClauses (cs : Clauses) : (UnitClauses × Clauses) :=
  go cs [] []
where
  go (cs : Clauses) (units : UnitClauses) (others : Clauses) : (UnitClauses × Clauses) :=
    match cs with
    | [] => (units, others)
    | c :: cs =>
      if c.size == 1 then
        let lit := c.pop!
        go cs (lit :: units) others
      else
        go cs units (c :: others)

/--
Propagate a single `unit` clause through a list of `Clauses`, outputting the remaining
`Clauses` as well as new `UnitClauses` that we produced.
-/
def unitPropagate (unit : Int) (clauses : Clauses) : LogM (UnitClauses × Clauses) := do
  log s!"Propagating {unit} into {clauses.toList}"
  let mut newUnits := []
  let mut remainder := []
  for clause in clauses do
    if clause.contains unit then
      pure ()
    else if clause.contains (-unit) then
      let newClause := clause.erase (-unit)
      if newClause.size == 1 then
        let lit := newClause.pop!
        newUnits := lit :: newUnits
      else
        remainder := newClause :: remainder
    else
      remainder := clause :: remainder
  return (newUnits, remainder)

set_option trace.compiler.ir.result true in
/--
Derive False by running `unitPropagate` on a list of `Clauses`.
-/
partial def deriveFalse (clauses : Clauses) (initialAssumptions : List Int := []) : LogM Bool := do
  log s!"Attempting to derive inconsistenty for {clauses.toList}"
  let (initialUnits, clauses) := partitionUnitClauses clauses
  go {} (initialAssumptions ++ initialUnits) clauses
where
  go (processedUnits : HashSet Int) (workList : UnitClauses) (clauses : Clauses) : LogM Bool := do
    match workList with
    | [] => return false
    | newUnit :: workList =>
      withAdditionalIndent 4 do
        log s!"Working on unit clause: {newUnit} next"
        log s!"Already processed unit clauses: {processedUnits.toList}"
        if processedUnits.contains (-newUnit) then
          log "Derived inconsistency"
          return true

        let (additionalUnits, clauses) ← unitPropagate newUnit clauses
        log s!"Derived additional units {additionalUnits}"
        log s!"Remaining clauses: {clauses.toList}"

        let processedUnits := processedUnits.insert newUnit
        let workList := additionalUnits ++ workList
        go processedUnits workList clauses

/--
Verify a RUP proof. Note that there exist two type of RUP proofs.
The first is an UNSAT certificate. It contains an empty clause in the end,
signalling the goal to derive false (and thus UNSAT) from the current knowledge.
The other kind just wants to proof some sort of clause follows from the DIMACS ones,
it simply ends on that clause.

This function is capable of verifying both.
-/
partial def verify (known : Clauses) (todo : Clauses) : LogM RupResult := do
  match todo with
  | [] =>
    log "Verification finished, no more goals remaining"
    -- If we arrive here we are not dealing with an UNSAT proof and have no goals left
    -- We thus succeeded in verifying a "just prove some clause" RUP proof.
    return .success
  | new :: remaining =>
    if new.size == 0 then
      log s!"Proving the final step of this UNSAT proof"
      -- We just met an empty clause as a goal. This means we are verifying an UNSAT
      -- proof and need to derive false from our current knowledge to finish.
      if ← withAdditionalIndent 4 do deriveFalse known then
        return .success
      else
        return .failure
    else
      log s!"Proving next goal: {new.toList}, based on {known.toList}"
      -- We are still along the lines of verifying some proof chain.
      -- Attempt to derive false by adding the negation of the current RUP goal
      -- to the list of known terms and running unit propagation to derive false.
      -- If this succeeds we have proven the goal and can add it to our list of known
      -- facts. Otherwise we are stuck and give up.
      if ← withAdditionalIndent 4 do deriveFalse known new.negation then
        verify (new :: known) remaining
      else
        return .stuck

def main (args : List String) : IO UInt32 := do
  -- Verification stonks
  if args.length >= 2 then
    IO.println "Reading input files..."
    let dimacsInput ← IO.FS.readFile args[0]!
    let rupInput ← IO.FS.readFile args[1]!
    IO.println "Parsing input files..."
    let dimacs ← IO.ofExcept <| parseDimacs.run dimacsInput
    let rup ← IO.ofExcept <| parseRup.run rupInput
    IO.println "Checking proof..."
    let cfg ←
      if args.length == 3 then
        let additionalArg := args[2]!
        if additionalArg == "nolog" then
          pure { indent := 0, active := false }
        else
          throw <| .userError s!"Unknown argument: {additionalArg}"
      else
          pure { indent := 0, active := true }
    let result ← verify dimacs rup |>.run cfg
    match result with
    | .success =>
      IO.println "Proof correct!"
      return 0
    | .stuck =>
      IO.println "Got stuck while verifying"
      return 2
    | .failure =>
      IO.println "Failed to show false from the given RUP clauses"
      return 3
  else
    IO.println "I expecte precisely two arguments: crup <dimacs-path> <rup-path>"
    return 1
