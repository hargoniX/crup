import Lean.Data.Parsec
import Lean.Data.HashSet
open Lean Parsec

/--
Pop an element from a `Lean.HashSet`, this function is sadly not implemented in core (yet).
-/
def Lean.HashSet.pop! [BEq α] [Hashable α] [Inhabited α] (set : HashSet α) : α :=
  -- There is sadly no pop so we do a little hack. The idea here is that we only ever call this function
  -- on singleton sets anyways so it doesn't matter that we iterate over the entire set with fold
  set.fold (init := none) (fun _ lit => some lit) |>.get!

-- Despite the main operation on Clauses being to check if they contain a unit clause or not, they are usually
-- so small in memory that the caching effects of Array outweigh the asymptotic performance of HashSet.
abbrev Clause := Array Int
-- Since we frequently add and remove elements to the list of clauses this is a List and not an Array
abbrev Clauses := List Clause

-- The unit clauses only get added to and we don't care about previous versions
abbrev UnitClauses := List Int

def Clause.toList (c : Clause) : List Int := Array.toList c
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
  go (clause : Clause) : Parsec Clause := do
    let nextLit ← parseLit
    if nextLit == 0 then
      ws
      return clause
    else
      ws
      go (clause.push nextLit)

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
  level : Nat

abbrev LogM (α) := ReaderT LogCfg IO α

@[inline]
def withAdditionalIndent (additional : Nat) (x : LogM α) : LogM α :=
  withReader (fun cfg => { cfg with indent := cfg.indent + additional }) x

@[macro_inline]
def log (x : String) (level : Nat := 1) : LogM Unit := do
  let cfg ← read
  if level >= cfg.level then
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
  c.foldl (init := []) (fun cs lit => (-lit) :: cs)

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
      if h : c.size == 1 then
        let lit := c[0]'(by simp_all_arith)
        go cs (lit :: units) others
      else
        go cs units (c :: others)

/--
Propagate a single `unit` clause through a list of `Clauses`, outputting the remaining
`Clauses` as well as new `UnitClauses` that we produced.
-/
def unitPropagate (unit : Int) (clauses : Clauses) : LogM (UnitClauses × Clauses) := do
  log s!"Propagating {unit} into {clauses.toList}"
  return go clauses [] []
where
  go (clauses : Clauses) (newUnits : UnitClauses) (remainder : Clauses) : UnitClauses × Clauses :=
    match clauses with
    | [] =>
      -- No clauses that we didn't propagate into yet, we are done
      (newUnits, remainder)
    | clause :: clauses =>
      -- Check if the current clause contains unit or -unit or neither, acting accordingly
      if clause.contains unit then
        go clauses newUnits remainder
      else if clause.contains (-unit) then
        -- We detect new unit clauses on the fly at this point already
        let newClause := clause.erase (-unit)
        if h : newClause.size == 1 then
          let lit := newClause[0]'(by simp_all_arith)
          go clauses (lit :: newUnits) remainder
        else
          go clauses newUnits (newClause :: remainder)
      else
        go clauses newUnits (clause :: remainder)

def List.containsBounded [BEq α] (xs : List α) (a : α) (bound : Nat) : Bool :=
  match xs, bound with
  | [], _ => false
  | _, 0 => false
  | x :: xs, n + 1 =>
    if x == a then
      true
    else
      List.containsBounded xs x n

/--
Derive False by running `unitPropagate` on a list of `Clauses`.
-/
partial def deriveFalse (clauses : Clauses) (initialAssumptions : UnitClauses := []) : LogM Bool := do
  let (initialUnits, clauses) := partitionUnitClauses clauses
  let units := initialAssumptions ++ initialUnits
  log s!"Attempting to derive inconsistency for {clauses.toList}, using unit clauses {units }"
  go {} (initialAssumptions ++ initialUnits) clauses
where
  go (processedUnits : HashSet Int) (workList : UnitClauses) (clauses : Clauses) : LogM Bool := do
    match workList with
    | [] => return false
    | newUnit :: workList =>
      withAdditionalIndent 4 do
        log s!"Working on unit clause: {newUnit} next"
        log s!"Known unit clauses: {processedUnits.toList}, {workList}"
        -- The procedure is still complete if we do not check the workList here,
        -- as all elements eventually end up to processedUnits. Since the worklist
        -- can in theory end up containing the vast majority of literals we limit
        -- the search to a (somewhat arbitrary) constant in order to avoid searching
        -- a large linked list over and over again.
        -- Note that this doesn't catch all inconsitencies, even if the workList is bounded at 64 elements.
        -- This is because we do not look for inconsistencies in the worklist itself.
        -- That check only ever fires once we pull the first inconsitent element from the worklist.
        if processedUnits.contains (-newUnit) || workList.containsBounded (-newUnit) 64 then
          log "Derived inconsistency"
          return true
        let (additionalUnits, clauses) ← unitPropagate newUnit clauses
        log s!"Derived additional units: {additionalUnits}"
        let workList := additionalUnits ++ workList
        log s!"Now remaining units: {workList}"
        log s!"Now remaining clauses: {clauses.toList}"

        let processedUnits := processedUnits.insert newUnit
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
      log (level := 2) s!"Proving the final step of this UNSAT proof"
      -- We just met an empty clause as a goal. This means we are verifying an UNSAT
      -- proof and need to derive false from our current knowledge to finish.
      if ← withAdditionalIndent 4 do deriveFalse known then
        return .success
      else
        return .failure
    else
      log (level := 2) s!"Proving next goal: {new.toList}"
      log s!"Using current knowledge: {known.toList} "
      -- We are still along the lines of verifying some proof chain.
      -- Attempt to derive false by adding the negation of the current RUP goal
      -- to the list of known terms and running unit propagation to derive false.
      -- If this succeeds we have proven the goal and can add it to our list of known
      -- facts. Otherwise we are stuck and give up.
      if ← withAdditionalIndent 4 do deriveFalse known new.negation then
        log (level := 2) s!"Clause proven redudant: {new.toList}"
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
        match additionalArg.toNat? with
        | none =>
          throw <| .userError s!"The third argument must be a Nat log level but was: {additionalArg}"
        | some level =>
          pure { indent := 0, level := level }
      else
          pure { indent := 0, level := 1 }
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
