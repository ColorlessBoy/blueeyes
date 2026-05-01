import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# The red-eyes / green-eyes puzzle

This file formalizes a small Kripke-style epistemic model for the classic
public-announcement logic puzzle, then proves the counting induction at the
heart of the usual solution.

The informal story is:

* everyone can see everybody else's eye color, but not their own;
* the guru publicly announces that at least one person has red eyes;
* if somebody can infer that they have red eyes, they leave that night;
* if nobody leaves for several nights, that absence is also public information.

The first layer defines worlds, observations, knowledge, public announcements,
and the update caused by a night in which nobody leaves.  The second layer is the
counting quotient used in the classic hand proof: after `k` quiet nights, every
world with at most `k` red-eyed people has been eliminated.
-/

namespace BlueEyes

/-- The two eye colors used in the story. -/
inductive EyeColor where
  | red
  | green
  deriving DecidableEq, Repr

/-! ## Epistemic model -/

/-- A world assigns an eye color to every agent. -/
structure World (Agent : Type u) where
  color : Agent → EyeColor

/-- A proposition is a predicate on worlds. -/
abbrev Propn (Agent : Type u) :=
  World Agent → Prop

/-- A model is the set of worlds still considered possible by public information. -/
abbrev Model (Agent : Type u) :=
  World Agent → Prop

/--
Agent `i` cannot distinguish `w` from `v` exactly when every other agent has the
same color in both worlds.  The agent's own color is deliberately ignored.
-/
def indistinguishable (i : Agent) (w v : World Agent) : Prop :=
  ∀ j, j ≠ i → v.color j = w.color j

/-- In model `M`, agent `i` knows proposition `P` at world `w`. -/
def Knows (M : Model Agent) (i : Agent) (w : World Agent) (P : Propn Agent) : Prop :=
  ∀ v, M v → indistinguishable i w v → P v

/-- The proposition that agent `i` is red-eyed. -/
def IsRed (i : Agent) : Propn Agent :=
  fun w => w.color i = EyeColor.red

/-- The proposition that at least one agent is red-eyed. -/
def AtLeastOneRed (w : World Agent) : Prop :=
  ∃ i, w.color i = EyeColor.red

/-- The unconstrained starting model: every color assignment is possible. -/
def initialModel : Model Agent :=
  fun _ => True

/-- Publicly announcing `A` restricts the current model to worlds satisfying `A`. -/
def publicAnnouncement (M : Model Agent) (A : Propn Agent) : Model Agent :=
  fun w => M w ∧ A w

/-- The model immediately after the guru announces that at least one person is red-eyed. -/
def afterGuruAnnouncement : Model Agent :=
  publicAnnouncement initialModel AtLeastOneRed

/-- The guru announcement removes exactly the worlds with no red-eyed agent. -/
theorem afterGuruAnnouncement_iff {w : World Agent} :
    afterGuruAnnouncement w ↔ AtLeastOneRed w := by
  simp [afterGuruAnnouncement, publicAnnouncement, initialModel]

/-- Agent `i` would leave in world `w` if they know that their own eyes are red. -/
def WouldLeave (M : Model Agent) (i : Agent) (w : World Agent) : Prop :=
  Knows M i w (IsRed i)

/-- A quiet night is one in which no agent knows that they are red-eyed. -/
def QuietNight (M : Model Agent) : Propn Agent :=
  fun w => ∀ i, ¬ WouldLeave M i w

/--
Update the public model after one quiet night.  Worlds where somebody would have
known they were red-eyed are removed.
-/
def afterOneQuietNight (M : Model Agent) : Model Agent :=
  publicAnnouncement M (QuietNight M)

/-- One quiet-night update keeps exactly the worlds in which nobody would leave. -/
theorem afterOneQuietNight_iff {M : Model Agent} {w : World Agent} :
    afterOneQuietNight M w ↔ M w ∧ ∀ i, ¬ WouldLeave M i w := by
  rfl

/--
The public model after the guru announcement and `n` consecutive quiet nights.
This is the dynamic-epistemic part of the puzzle: absence of departures becomes
new public information each night.
-/
def afterQuietNights : Nat → Model Agent
  | 0 => afterGuruAnnouncement
  | n + 1 => afterOneQuietNight (afterQuietNights n)

/-- Zero quiet nights means only the guru's announcement has been applied. -/
theorem afterQuietNights_zero :
    afterQuietNights (Agent := Agent) 0 = afterGuruAnnouncement :=
  rfl

/-- The successor step is one more public update by the fact that nobody left. -/
theorem afterQuietNights_succ (n : Nat) :
    afterQuietNights (Agent := Agent) (n + 1) =
      afterOneQuietNight (afterQuietNights (Agent := Agent) n) :=
  rfl

/-- Recolor only agent `i`, leaving all other observations unchanged. -/
def recolorSelf [DecidableEq Agent] (i : Agent) (c : EyeColor) (w : World Agent) :
    World Agent where
  color := fun j => if j = i then c else w.color j

/-- Recoloring only one's own eyes is observationally invisible to that agent. -/
theorem indistinguishable_recolorSelf [DecidableEq Agent] (i : Agent) (c : EyeColor)
    (w : World Agent) :
    indistinguishable i w (recolorSelf i c w) := by
  intro j hj
  simp [recolorSelf, hj]

/-- Recoloring oneself to red makes `IsRed i` true in the recolored world. -/
theorem isRed_recolorSelf_red [DecidableEq Agent] (i : Agent) (w : World Agent) :
    IsRed i (recolorSelf i EyeColor.red w) := by
  simp [IsRed, recolorSelf]

/-- Recoloring oneself to green makes `IsRed i` false in the recolored world. -/
theorem not_isRed_recolorSelf_green [DecidableEq Agent] (i : Agent) (w : World Agent) :
    ¬ IsRed i (recolorSelf i EyeColor.green w) := by
  simp [IsRed, recolorSelf]

/--
The basic reason knowledge is nontrivial in this puzzle: if an agent's green-eyed
self-variant is still in the model, then they cannot know that they are red-eyed.
-/
theorem not_knows_red_if_green_variant_possible [DecidableEq Agent] {M : Model Agent}
    {i : Agent} {w : World Agent} (hgreen : M (recolorSelf i EyeColor.green w)) :
    ¬ Knows M i w (IsRed i) := by
  intro hknow
  exact not_isRed_recolorSelf_green i w
    (hknow (recolorSelf i EyeColor.green w) hgreen
      (indistinguishable_recolorSelf i EyeColor.green w))

/-- Knowledge is monotone with respect to logical implication inside a model. -/
theorem Knows.mono {M : Model Agent} {i : Agent} {w : World Agent} {P Q : Propn Agent}
    (hknow : Knows M i w P) (himp : ∀ v, M v → P v → Q v) :
    Knows M i w Q := by
  intro v hvM hvobs
  exact himp v hvM (hknow v hvM hvobs)

/-! ## Common knowledge as a fixed point -/

/-- Everybody knows proposition `P` at world `w`. -/
def EveryoneKnows (M : Model Agent) (w : World Agent) (P : Propn Agent) : Prop :=
  ∀ i, Knows M i w P

/--
`n` levels of mutual knowledge.  Level `0` is just `P`; level `n + 1` says that
everybody knows level `n`.
-/
def IteratedEveryoneKnows (M : Model Agent) (P : Propn Agent) :
    Nat → Propn Agent
  | 0 => P
  | n + 1 => fun w => EveryoneKnows M w (IteratedEveryoneKnows M P n)

/--
Common knowledge is the greatest fixed-point presentation used in modal logic:
`P` is common knowledge when every finite level of mutual knowledge holds.
-/
def CommonKnowledge (M : Model Agent) (P : Propn Agent) : Propn Agent :=
  fun w => ∀ n, IteratedEveryoneKnows M P n w

/-- Common knowledge implies the announced fact itself. -/
theorem CommonKnowledge.base {M : Model Agent} {P : Propn Agent} {w : World Agent}
    (h : CommonKnowledge M P w) :
    P w :=
  h 0

/--
The fixed-point unfolding: `P` is common knowledge iff `P` is true and everybody
knows that `P` is common knowledge.
-/
theorem commonKnowledge_unfold {M : Model Agent} {P : Propn Agent} {w : World Agent} :
    CommonKnowledge M P w ↔ P w ∧ EveryoneKnows M w (CommonKnowledge M P) := by
  constructor
  · intro h
    constructor
    · exact h 0
    · intro i v hvM hobs n
      cases n with
      | zero =>
          exact h 1 i v hvM hobs
      | succ n =>
          exact h (n + 2) i v hvM hobs
  · intro h n
    cases n with
    | zero =>
        exact h.1
    | succ n =>
        intro i v hvM hobs
        exact h.2 i v hvM hobs n

/-! ## Explicit departure-state transitions -/

/--
A dynamic state records the current public model and which agents are still
present.  The color world is not stored here; transitions are parameterized by
the actual world whose departures are observed.
-/
structure NightState (Agent : Type u) where
  model : Model Agent
  present : Agent → Prop

/-- The state immediately after the guru's announcement, before any night passes. -/
def initialNightState : NightState Agent where
  model := afterGuruAnnouncement
  present := fun _ => True

/-- In a state, an agent leaves exactly when they are present and know they are red. -/
def WouldLeaveInState (S : NightState Agent) (i : Agent) (w : World Agent) : Prop :=
  S.present i ∧ WouldLeave S.model i w

/-- The actual departure report generated by state `S` in world `w`. -/
def departureReport (S : NightState Agent) (w : World Agent) : Agent → Prop :=
  fun i => WouldLeaveInState S i w

/--
Updating the model by a public departure report keeps exactly the worlds whose
predicted leavers match the observed report.
-/
def updateModelByReport (M : Model Agent) (present report : Agent → Prop) : Model Agent :=
  fun w => M w ∧ ∀ i, report i ↔ present i ∧ WouldLeave M i w

/-- Advance one night after observing the departure report generated by `actual`. -/
def nextNightState (S : NightState Agent) (actual : World Agent) : NightState Agent where
  model := updateModelByReport S.model S.present (departureReport S actual)
  present := fun i => S.present i ∧ ¬ departureReport S actual i

/-- If the observed departure report is empty, the model update is the quiet-night update. -/
theorem updateModelBy_empty_report_eq_quiet {M : Model Agent} :
    updateModelByReport M (fun _ : Agent => True) (fun _ => False) =
      afterOneQuietNight M := by
  funext w
  apply propext
  constructor
  · intro h
    constructor
    · exact h.1
    · intro i hleave
      exact (h.2 i).mpr ⟨trivial, hleave⟩
  · intro h
    constructor
    · exact h.1
    · intro i
      constructor
      · intro hfalse
        cases hfalse
      · intro hleave
        exact False.elim (h.2 i hleave.2)

/-! ## Counting abstraction -/

/--
Before using the public information from quiet nights, a person who sees `seen`
red-eyed people considers exactly two total red-eye counts possible:

* `seen`: they themselves are not red-eyed;
* `seen + 1`: they themselves are red-eyed.
-/
def compatibleWithObservation (seen totalRed : Nat) : Prop :=
  totalRed = seen ∨ totalRed = seen + 1

/-! ## Finite worlds and concrete red-eye counts -/

section FiniteCounting

variable [Fintype Agent] [DecidableEq Agent]

/-- The finite set of red-eyed agents in a world. -/
def redAgents (w : World Agent) : Finset Agent :=
  Finset.univ.filter fun i => w.color i = EyeColor.red

/-- The total number of red-eyed agents in a world. -/
def totalRed (w : World Agent) : Nat :=
  (redAgents w).card

/-- The finite set of red-eyed agents visible to `i`; their own eye color is removed. -/
def visibleRedAgents (i : Agent) (w : World Agent) : Finset Agent :=
  (redAgents w).erase i

/-- The number of red-eyed agents visible to `i`. -/
def seenRed (i : Agent) (w : World Agent) : Nat :=
  (visibleRedAgents i w).card

omit [DecidableEq Agent] in
/-- Membership in `redAgents` is exactly redness in the world. -/
theorem mem_redAgents_iff {w : World Agent} {i : Agent} :
    i ∈ redAgents w ↔ IsRed i w := by
  simp [redAgents, IsRed]

/-- Observationally indistinguishable worlds have the same visible red agents. -/
theorem visibleRedAgents_eq_of_indistinguishable {i : Agent} {w v : World Agent}
    (hobs : indistinguishable i w v) :
    visibleRedAgents i v = visibleRedAgents i w := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [visibleRedAgents]
  · simp [visibleRedAgents, redAgents, hobs j hj]

/-- Observationally indistinguishable worlds have the same visible red count. -/
theorem seenRed_eq_of_indistinguishable {i : Agent} {w v : World Agent}
    (hobs : indistinguishable i w v) :
    seenRed i v = seenRed i w := by
  simp [seenRed, visibleRedAgents_eq_of_indistinguishable hobs]

/-- A red-eyed agent contributes one more red eye than they can see. -/
theorem totalRed_eq_seenRed_add_one_of_red {i : Agent} {w : World Agent}
    (hred : IsRed i w) :
    totalRed w = seenRed i w + 1 := by
  have hi : i ∈ redAgents w := by
    simpa [mem_redAgents_iff] using hred
  have hcard := Finset.card_erase_add_one (s := redAgents w) (a := i) hi
  exact hcard.symm

/-- A non-red-eyed agent sees all red-eyed agents. -/
theorem totalRed_eq_seenRed_of_not_red {i : Agent} {w : World Agent}
    (hgreen : ¬ IsRed i w) :
    totalRed w = seenRed i w := by
  have hi : i ∉ redAgents w := by
    intro hi
    exact hgreen ((mem_redAgents_iff).mp hi)
  have herase := Finset.erase_eq_of_notMem (a := i) (s := redAgents w) hi
  simp [totalRed, seenRed, visibleRedAgents, herase]

/--
The concrete world model justifies the two-count abstraction: from agent `i`'s
perspective, the total red count is either the number they see or that number
plus one.
-/
theorem compatibleWithConcreteObservation (i : Agent) (w : World Agent) :
    compatibleWithObservation (seenRed i w) (totalRed w) := by
  by_cases hred : IsRed i w
  · exact Or.inr (totalRed_eq_seenRed_add_one_of_red (i := i) (w := w) hred)
  · exact Or.inl (totalRed_eq_seenRed_of_not_red (i := i) (w := w) hred)

omit [DecidableEq Agent] in
/-- The guru's announcement gives a positive concrete red-eye count. -/
theorem totalRed_pos_of_atLeastOneRed {w : World Agent} (h : AtLeastOneRed w) :
    0 < totalRed w := by
  rcases h with ⟨i, hi⟩
  have hmem : i ∈ redAgents w := by
    simpa [redAgents, IsRed] using hi
  exact Finset.card_pos.mpr ⟨i, hmem⟩

/--
The central bridge from the Kripke update semantics to the counting solution:
after `n` quiet nights, every remaining concrete finite world has more than `n`
red-eyed agents.
-/
theorem afterQuietNights_count_lower_bound :
    ∀ n {w : World Agent}, afterQuietNights (Agent := Agent) n w → n < totalRed w
  | 0, w, hw => by
      exact totalRed_pos_of_atLeastOneRed ((afterGuruAnnouncement_iff).mp hw)
  | n + 1, w, hw => by
      rcases hw with ⟨hwPrev, hquiet⟩
      have ihw : n < totalRed w := afterQuietNights_count_lower_bound n hwPrev
      by_contra hnot
      have hle : totalRed w ≤ n + 1 := Nat.le_of_not_gt hnot
      have htotal : totalRed w = n + 1 := by omega
      have hpos : 0 < (redAgents w).card := by
        simpa [totalRed] using (by omega : 0 < totalRed w)
      rcases (Finset.card_pos.mp hpos) with ⟨i, hi⟩
      have hred : IsRed i w := (mem_redAgents_iff).mp hi
      have hleave : WouldLeave (afterQuietNights (Agent := Agent) n) i w := by
        intro v hvM hobs
        by_contra hgreen
        have hseen : seenRed i v = seenRed i w :=
          seenRed_eq_of_indistinguishable hobs
        have hvTotal : totalRed v = seenRed i v :=
          totalRed_eq_seenRed_of_not_red (i := i) (w := v) hgreen
        have hwTotal : totalRed w = seenRed i w + 1 :=
          totalRed_eq_seenRed_add_one_of_red (i := i) (w := w) hred
        have ihv : n < totalRed v := afterQuietNights_count_lower_bound n hvM
        omega
      exact hquiet i hleave

/-- Worlds with at most `n` red-eyed agents cannot survive `n` Kripke quiet updates. -/
theorem not_afterQuietNights_of_totalRed_le
    {n : Nat} {w : World Agent} (hle : totalRed w ≤ n) :
    ¬ afterQuietNights (Agent := Agent) n w := by
  intro hw
  have hlt : n < totalRed w := afterQuietNights_count_lower_bound n hw
  omega

/--
A red-eyed agent leaves after exactly as many quiet nights as the number of
red-eyed agents they can see.  This is the concrete Kripke-level version of the
classic induction step.
-/
theorem redAgent_wouldLeave_after_seenQuietNights
    {i : Agent} {w : World Agent} (_hred : IsRed i w)
    (_hw : afterQuietNights (Agent := Agent) (seenRed i w) w) :
    WouldLeave (afterQuietNights (Agent := Agent) (seenRed i w)) i w := by
  intro v hvM hobs
  by_contra hgreen
  have hseen : seenRed i v = seenRed i w :=
    seenRed_eq_of_indistinguishable hobs
  have hvTotal : totalRed v = seenRed i v :=
    totalRed_eq_seenRed_of_not_red (i := i) (w := v) hgreen
  have ihv : seenRed i w < totalRed v :=
    afterQuietNights_count_lower_bound (seenRed i w) hvM
  omega

/--
All red-eyed agents leave on the same decisive night, namely after
`totalRed w - 1` quiet nights.  This theorem states the positive part of the
story conclusion: every red-eyed agent would leave in that public model.
-/
theorem allRedAgents_wouldLeave_on_decisiveNight
    {w : World Agent} (hw : afterQuietNights (Agent := Agent) (totalRed w - 1) w) :
    ∀ i, IsRed i w → WouldLeave (afterQuietNights (Agent := Agent) (totalRed w - 1)) i w := by
  intro i hred
  have htotal : totalRed w = seenRed i w + 1 :=
    totalRed_eq_seenRed_add_one_of_red (i := i) (w := w) hred
  have hnight : totalRed w - 1 = seenRed i w := by omega
  rw [hnight] at hw ⊢
  exact redAgent_wouldLeave_after_seenQuietNights (i := i) (w := w) hred hw

end FiniteCounting

/-! ## Counting quotient of the epistemic model -/

/--
After the guru's announcement and `quietNights` nights with no departures, a total
red-eye count remains possible for a person seeing `seen` red-eyed people exactly
when:

* it is compatible with their visual observation;
* it satisfies the guru's announcement, namely `0 < totalRed`;
* it has not been eliminated by the public fact that nobody left during the first
  `quietNights` nights, namely `quietNights < totalRed`.
-/
def possibleAfterQuietNights (quietNights seen totalRed : Nat) : Prop :=
  compatibleWithObservation seen totalRed ∧ 0 < totalRed ∧ quietNights < totalRed

/--
The counting abstraction associated with a concrete epistemic model.  It records
only the number of red-eyed people an agent sees and the total number of red-eyed
people in a world.  The bridge condition states that the concrete observation
relation has collapsed to the two expected total-count possibilities.
-/
structure CountingView where
  seen : Nat
  totalRed : Nat
  compatible : compatibleWithObservation seen totalRed

/-- The counting view generated by a concrete finite world and an observing agent. -/
def concreteCountingView [Fintype Agent] [DecidableEq Agent] (i : Agent) (w : World Agent) :
    CountingView where
  seen := seenRed i w
  totalRed := totalRed w
  compatible := compatibleWithConcreteObservation i w

/--
Public information after `quietNights` nights, expressed at the counting level.
This is the quotient of `afterQuietNights`: the guru announcement gives
`0 < totalRed`, while quiet nights give `quietNights < totalRed`.
-/
def countingViewPossibleAfterQuietNights (quietNights : Nat) (view : CountingView) : Prop :=
  0 < view.totalRed ∧ quietNights < view.totalRed

/-- The structured counting view implies the simpler predicate used below. -/
theorem possible_of_countingView {quietNights : Nat} {view : CountingView}
    (h : countingViewPossibleAfterQuietNights quietNights view) :
    possibleAfterQuietNights quietNights view.seen view.totalRed := by
  exact ⟨view.compatible, h.1, h.2⟩

/--
Concrete worlds enter the counting quotient through `concreteCountingView`.  The
only extra public facts needed at this level are the guru announcement and the
quiet-night lower bound on the total red count.
-/
theorem possibleAfterQuietNights_of_concrete [Fintype Agent] [DecidableEq Agent]
    {quietNights : Nat} {i : Agent} {w : World Agent}
    (hann : AtLeastOneRed w) (hquiet : quietNights < totalRed w) :
    possibleAfterQuietNights quietNights (seenRed i w) (totalRed w) := by
  exact ⟨compatibleWithConcreteObservation i w, totalRed_pos_of_atLeastOneRed hann, hquiet⟩

/--
Concrete remaining Kripke worlds automatically enter the counting predicate.  In
particular, the lower bound `n < totalRed w` is not an external assumption here;
it is derived from the repeated quiet-night updates.
-/
theorem possibleAfterQuietNights_of_afterQuietNights [Fintype Agent] [DecidableEq Agent]
    {n : Nat} {i : Agent} {w : World Agent}
    (hw : afterQuietNights (Agent := Agent) n w) :
    possibleAfterQuietNights n (seenRed i w) (totalRed w) := by
  have hlt : n < totalRed w := afterQuietNights_count_lower_bound n hw
  exact ⟨compatibleWithConcreteObservation i w, by omega, hlt⟩

/--
In a concrete finite world, a red-eyed agent's own world satisfies the counting
predicate at the decisive night: the number of quiet nights is exactly the
number of red-eyed people they see.
-/
theorem possibleAfterConcreteRedSeenQuietNights [Fintype Agent] [DecidableEq Agent]
    {i : Agent} {w : World Agent} (hred : IsRed i w) :
    possibleAfterQuietNights (seenRed i w) (seenRed i w) (totalRed w) := by
  have htotal := totalRed_eq_seenRed_add_one_of_red (i := i) (w := w) hred
  refine ⟨compatibleWithConcreteObservation i w, ?_, ?_⟩
  · exact totalRed_pos_of_atLeastOneRed ⟨i, hred⟩
  · omega

/--
Concrete version of the decisive-night conclusion: if a red-eyed agent sees
`seenRed i w` red-eyed people, then after that many quiet nights any remaining
compatible total count must be the actual total red count of `w`.
-/
theorem redEyedPerson_knows_concrete_total [Fintype Agent] [DecidableEq Agent]
    {i : Agent} {w : World Agent} {candidateTotal : Nat} (hred : IsRed i w)
    (hpossible :
      possibleAfterQuietNights (seenRed i w) (seenRed i w) candidateTotal) :
    candidateTotal = totalRed w := by
  have hactual := totalRed_eq_seenRed_add_one_of_red (i := i) (w := w) hred
  rcases hpossible with ⟨hobs, _hann, hquiet⟩
  rcases hobs with hnotRed | hredCandidate
  · omega
  · omega

/--
If the actual number of red-eyed people is `r`, then a red-eyed person sees
`r - 1` red-eyed people.  After `r - 1` quiet nights, the alternative world where
they are not red-eyed has been eliminated, so every remaining compatible world
has total count `r`.
-/
theorem redEyedPerson_knows_after_quietNights (r totalRed : Nat) (hr : 0 < r) :
    possibleAfterQuietNights (r - 1) (r - 1) totalRed → totalRed = r := by
  intro h
  rcases h with ⟨hobs, _hann, hquiet⟩
  rcases hobs with hnotRed | hred
  · omega
  · omega

/--
The base case of the puzzle: if a red-eyed person sees no red-eyed people, the
guru's announcement immediately rules out the possibility that they are not
red-eyed.  They can leave on the first night.
-/
theorem oneRedPerson_knows_immediately (totalRed : Nat) :
    possibleAfterQuietNights 0 0 totalRed → totalRed = 1 := by
  simpa using redEyedPerson_knows_after_quietNights 1 totalRed (by omega)

/--
The `n + 1` person version stated with `n` as the number of other red-eyed people
that a red-eyed person sees.  After `n` quiet nights, they know that the total
number of red-eyed people is `n + 1`, hence they are red-eyed.
-/
theorem redEyedPerson_knows_after_seeing_n (n totalRed : Nat) :
    possibleAfterQuietNights n n totalRed → totalRed = n + 1 := by
  intro h
  rcases h with ⟨hobs, _hann, hquiet⟩
  rcases hobs with hnotRed | hred
  · omega
  · omega

/--
A green-eyed person seeing `r` red-eyed people does *not* get the same conclusion
after only `r - 1` quiet nights: both `r` and `r + 1` remain compatible with what
they see and with the public information.

This captures why exactly the red-eyed people, and not the green-eyed people,
leave on the decisive night.
-/
theorem greenEyedPerson_still_has_two_possibilities (r : Nat) (hr : 0 < r) :
    possibleAfterQuietNights (r - 1) r r ∧
      possibleAfterQuietNights (r - 1) r (r + 1) := by
  constructor
  · constructor
    · exact Or.inl rfl
    · constructor
      · exact hr
      · omega
  · constructor
    · exact Or.inr rfl
    · constructor
      · omega
      · omega

/--
The public-announcement induction as a reusable lemma: after `quietNights` nights
with no departures, every still-possible world has more than `quietNights`
red-eyed people.
-/
theorem possible_totalRed_gt_quietNights {quietNights seen totalRed : Nat}
    (h : possibleAfterQuietNights quietNights seen totalRed) :
    quietNights < totalRed :=
  h.2.2

/--
Equivalently, any world with at most `quietNights` red-eyed people has been ruled
out by `quietNights` nights with no departures.
-/
theorem eliminated_by_quietNights {quietNights seen totalRed : Nat}
    (hle : totalRed ≤ quietNights) :
    ¬ possibleAfterQuietNights quietNights seen totalRed := by
  intro h
  exact Nat.not_lt_of_ge hle h.2.2

/-! ## Concrete three-islander example -/

/-- A concrete world with three islanders: islanders `0` and `1` are red, `2` is green. -/
def twoRedOneGreen : World (Fin 3) where
  color
    | 0 => EyeColor.red
    | 1 => EyeColor.red
    | 2 => EyeColor.green

theorem twoRedOneGreen_red_zero : IsRed (0 : Fin 3) twoRedOneGreen := by
  rfl

theorem twoRedOneGreen_red_one : IsRed (1 : Fin 3) twoRedOneGreen := by
  rfl

theorem twoRedOneGreen_not_red_two : ¬ IsRed (2 : Fin 3) twoRedOneGreen := by
  intro h
  cases h

theorem twoRedOneGreen_totalRed : totalRed twoRedOneGreen = 2 := by
  decide

theorem twoRedOneGreen_seenRed_zero : seenRed (0 : Fin 3) twoRedOneGreen = 1 := by
  decide

theorem twoRedOneGreen_seenRed_one : seenRed (1 : Fin 3) twoRedOneGreen = 1 := by
  decide

theorem twoRedOneGreen_seenRed_two : seenRed (2 : Fin 3) twoRedOneGreen = 2 := by
  decide

/-- In the two-red-one-green example, the first night is quiet. -/
theorem twoRedOneGreen_after_one_quiet_night :
    afterQuietNights (Agent := Fin 3) 1 twoRedOneGreen := by
  constructor
  · exact ⟨trivial, ⟨(0 : Fin 3), rfl⟩⟩
  · intro i hleave
    fin_cases i
    · exact (not_knows_red_if_green_variant_possible
        (M := afterGuruAnnouncement) (i := (0 : Fin 3)) (w := twoRedOneGreen)
        (by
          constructor
          · trivial
          · exact ⟨(1 : Fin 3), by simp [recolorSelf, twoRedOneGreen]⟩)) hleave
    · exact (not_knows_red_if_green_variant_possible
        (M := afterGuruAnnouncement) (i := (1 : Fin 3)) (w := twoRedOneGreen)
        (by
          constructor
          · trivial
          · exact ⟨(0 : Fin 3), by simp [recolorSelf, twoRedOneGreen]⟩)) hleave
    · exact twoRedOneGreen_not_red_two
        (hleave twoRedOneGreen ⟨trivial, ⟨(0 : Fin 3), rfl⟩⟩ (by intro j _hj; rfl))

/--
In the concrete `twoRedOneGreen` world, if the first night is quiet, both red-eyed
islanders would leave on the next night.
-/
theorem twoRedOneGreen_reds_leave_after_one_quiet_night
    (hw : afterQuietNights (Agent := Fin 3) 1 twoRedOneGreen) :
    WouldLeave (afterQuietNights (Agent := Fin 3) 1) (0 : Fin 3) twoRedOneGreen ∧
      WouldLeave (afterQuietNights (Agent := Fin 3) 1) (1 : Fin 3) twoRedOneGreen := by
  constructor
  · rw [← twoRedOneGreen_seenRed_zero] at hw ⊢
    exact redAgent_wouldLeave_after_seenQuietNights
      (i := (0 : Fin 3)) (w := twoRedOneGreen) twoRedOneGreen_red_zero hw
  · rw [← twoRedOneGreen_seenRed_one] at hw ⊢
    exact redAgent_wouldLeave_after_seenQuietNights
      (i := (1 : Fin 3)) (w := twoRedOneGreen) twoRedOneGreen_red_one hw

/-- In the concrete `twoRedOneGreen` world, the two red-eyed islanders leave together. -/
theorem twoRedOneGreen_reds_leave_together :
    WouldLeave (afterQuietNights (Agent := Fin 3) 1) (0 : Fin 3) twoRedOneGreen ∧
      WouldLeave (afterQuietNights (Agent := Fin 3) 1) (1 : Fin 3) twoRedOneGreen :=
  twoRedOneGreen_reds_leave_after_one_quiet_night twoRedOneGreen_after_one_quiet_night

/-! ## Why the public announcement matters -/

/-- A concrete two-islander world in which both islanders are red-eyed. -/
def allRedTwo : World (Fin 2) where
  color := fun _ => EyeColor.red

/-- The world obtained from `allRedTwo` by making islander `0` green. -/
def greenRedTwo : World (Fin 2) where
  color
    | 0 => EyeColor.green
    | 1 => EyeColor.red

/-- The world in which neither of the two islanders is red-eyed. -/
def allGreenTwo : World (Fin 2) where
  color := fun _ => EyeColor.green

theorem allRedTwo_everyoneKnows_atLeastOneRed :
    EveryoneKnows initialModel allRedTwo AtLeastOneRed := by
  intro i v _hv hobs
  fin_cases i
  · exact ⟨(1 : Fin 2), by simpa [allRedTwo] using hobs (1 : Fin 2) (by decide)⟩
  · exact ⟨(0 : Fin 2), by simpa [allRedTwo] using hobs (0 : Fin 2) (by decide)⟩

/--
Even in the actual world where both islanders are red-eyed, the bare initial
model does not make `AtLeastOneRed` common knowledge.  The obstruction is at the
second mutual-knowledge level: islander `0` considers `greenRedTwo` possible, and
in that world islander `1` considers the all-green world possible.
-/
theorem allRedTwo_not_commonKnowledge_atLeastOneRed :
    ¬ CommonKnowledge initialModel AtLeastOneRed allRedTwo := by
  intro hck
  have h0_knows_everyone_knows :
      Knows initialModel (0 : Fin 2) allRedTwo
        (EveryoneKnows initialModel · AtLeastOneRed) := by
    exact hck 2 (0 : Fin 2)
  have everyone_knows_in_greenRed :
      EveryoneKnows initialModel greenRedTwo AtLeastOneRed := by
    exact h0_knows_everyone_knows greenRedTwo trivial (by
      intro j hj
      fin_cases j
      · contradiction
      · decide)
  have atLeastOneRed_allGreen : AtLeastOneRed allGreenTwo := by
    exact everyone_knows_in_greenRed (1 : Fin 2) allGreenTwo trivial (by
      intro j hj
      fin_cases j
      · decide
      · contradiction)
  rcases atLeastOneRed_allGreen with ⟨i, hi⟩
  fin_cases i <;> simp [allGreenTwo] at hi

/--
Stronger phrasing of the same point: even though `EveryoneKnows initialModel
allRedTwo AtLeastOneRed` is true at the actual all-red world, it is not common
knowledge in the initial model that everybody knows there is a red-eyed person.
-/
theorem allRedTwo_not_commonKnowledge_everyoneKnows_atLeastOneRed :
    ¬ CommonKnowledge initialModel (fun w => EveryoneKnows initialModel w AtLeastOneRed)
      allRedTwo := by
  intro hck
  have everyone_knows_in_greenRed :
      EveryoneKnows initialModel greenRedTwo AtLeastOneRed := by
    exact hck 1 (0 : Fin 2) greenRedTwo trivial (by
      intro j hj
      fin_cases j
      · contradiction
      · decide)
  have atLeastOneRed_allGreen : AtLeastOneRed allGreenTwo := by
    exact everyone_knows_in_greenRed (1 : Fin 2) allGreenTwo trivial (by
      intro j hj
      fin_cases j
      · decide
      · contradiction)
  rcases atLeastOneRed_allGreen with ⟨i, hi⟩
  fin_cases i <;> simp [allGreenTwo] at hi

/-! ## Five all-red islanders: truth and knowledge still do not imply common knowledge -/

/--
For five islanders, `greenPrefixFive n` makes exactly those whose index is less
than `n` green-eyed, and the rest red-eyed.
-/
def greenPrefixFive (n : Nat) : World (Fin 5) where
  color i := if i.val < n then EyeColor.green else EyeColor.red

/-- The concrete world in which all five islanders are red-eyed. -/
def allRedFive : World (Fin 5) :=
  greenPrefixFive 0

/-- The concrete world in which all five islanders are green-eyed. -/
def allGreenFive : World (Fin 5) :=
  greenPrefixFive 5

theorem allRedFive_everyoneKnows_atLeastOneRed :
    EveryoneKnows initialModel allRedFive AtLeastOneRed := by
  intro i v _hv hobs
  fin_cases i
  · exact ⟨(1 : Fin 5), by simpa [allRedFive, greenPrefixFive] using hobs (1 : Fin 5) (by decide)⟩
  · exact ⟨(0 : Fin 5), by simpa [allRedFive, greenPrefixFive] using hobs (0 : Fin 5) (by decide)⟩
  · exact ⟨(0 : Fin 5), by simpa [allRedFive, greenPrefixFive] using hobs (0 : Fin 5) (by decide)⟩
  · exact ⟨(0 : Fin 5), by simpa [allRedFive, greenPrefixFive] using hobs (0 : Fin 5) (by decide)⟩
  · exact ⟨(0 : Fin 5), by simpa [allRedFive, greenPrefixFive] using hobs (0 : Fin 5) (by decide)⟩

/--
Even when all five islanders are actually red-eyed, `AtLeastOneRed` is not common
knowledge in the initial model.  The proof follows a five-step indistinguishability
chain:

`RRRRR ~ GRRRR ~ GGRRR ~ GGGRR ~ GGGGR ~ GGGGG`.
-/
theorem allRedFive_not_commonKnowledge_atLeastOneRed :
    ¬ CommonKnowledge initialModel AtLeastOneRed allRedFive := by
  intro hck
  have h1 :
      IteratedEveryoneKnows initialModel AtLeastOneRed 4 (greenPrefixFive 1) := by
    exact hck 5 (0 : Fin 5) (greenPrefixFive 1) trivial (by
      intro j hj
      fin_cases j <;> simp [allRedFive, greenPrefixFive] at hj ⊢)
  have h2 :
      IteratedEveryoneKnows initialModel AtLeastOneRed 3 (greenPrefixFive 2) := by
    exact h1 (1 : Fin 5) (greenPrefixFive 2) trivial (by
      intro j hj
      fin_cases j <;> simp [greenPrefixFive] at hj ⊢)
  have h3 :
      IteratedEveryoneKnows initialModel AtLeastOneRed 2 (greenPrefixFive 3) := by
    exact h2 (2 : Fin 5) (greenPrefixFive 3) trivial (by
      intro j hj
      fin_cases j <;> simp [greenPrefixFive] at hj ⊢)
  have h4 :
      IteratedEveryoneKnows initialModel AtLeastOneRed 1 (greenPrefixFive 4) := by
    exact h3 (3 : Fin 5) (greenPrefixFive 4) trivial (by
      intro j hj
      fin_cases j <;> simp [greenPrefixFive] at hj ⊢)
  have h5 : AtLeastOneRed allGreenFive := by
    exact h4 (4 : Fin 5) allGreenFive trivial (by
      intro j hj
      fin_cases j <;> simp [allGreenFive, greenPrefixFive] at hj ⊢)
  rcases h5 with ⟨i, hi⟩
  fin_cases i <;> simp [allGreenFive, greenPrefixFive] at hi

/--
The same five-person example phrased at the level the user asked about:
although the actual all-red world satisfies "everybody knows there is a red-eyed
person", that fact itself is not common knowledge without the public announcement.
-/
theorem allRedFive_not_commonKnowledge_everyoneKnows_atLeastOneRed :
    ¬ CommonKnowledge initialModel (fun w => EveryoneKnows initialModel w AtLeastOneRed)
      allRedFive := by
  intro hck
  have h1 :
      IteratedEveryoneKnows initialModel
        (fun w => EveryoneKnows initialModel w AtLeastOneRed) 3 (greenPrefixFive 1) := by
    exact hck 4 (0 : Fin 5) (greenPrefixFive 1) trivial (by
      intro j hj
      fin_cases j <;> simp [allRedFive, greenPrefixFive] at hj ⊢)
  have h2 :
      IteratedEveryoneKnows initialModel
        (fun w => EveryoneKnows initialModel w AtLeastOneRed) 2 (greenPrefixFive 2) := by
    exact h1 (1 : Fin 5) (greenPrefixFive 2) trivial (by
      intro j hj
      fin_cases j <;> simp [greenPrefixFive] at hj ⊢)
  have h3 :
      IteratedEveryoneKnows initialModel
        (fun w => EveryoneKnows initialModel w AtLeastOneRed) 1 (greenPrefixFive 3) := by
    exact h2 (2 : Fin 5) (greenPrefixFive 3) trivial (by
      intro j hj
      fin_cases j <;> simp [greenPrefixFive] at hj ⊢)
  have h4 :
      EveryoneKnows initialModel (greenPrefixFive 4) AtLeastOneRed := by
    exact h3 (3 : Fin 5) (greenPrefixFive 4) trivial (by
      intro j hj
      fin_cases j <;> simp [greenPrefixFive] at hj ⊢)
  have atLeastOneRed_allGreen : AtLeastOneRed allGreenFive := by
    exact h4 (4 : Fin 5) allGreenFive trivial (by
      intro j hj
      fin_cases j <;> simp [allGreenFive, greenPrefixFive] at hj ⊢)
  rcases atLeastOneRed_allGreen with ⟨i, hi⟩
  fin_cases i <;> simp [allGreenFive, greenPrefixFive] at hi

end BlueEyes
