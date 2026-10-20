import PearlDoCalculus.DSepSoundSkeleton
open PearlDoCalculus DAG Classical

variable {V : Type*} [DecidableEq V] [Fintype V]

inductive BallDir where
  | fromChild  : BallDir
  | fromParent : BallDir
  deriving DecidableEq, Repr

instance : Fintype BallDir := ⟨{.fromChild, .fromParent}, by intro x; cases x <;> simp⟩

structure BallState (V : Type*) where
  node : V
  dir  : BallDir
  deriving DecidableEq

def bbNext (G : DAG V) (Z anc : Finset V) (s t : BallState V) : Prop :=
  match s.dir with
  | .fromChild =>
    s.node ∉ Z ∧ (
      (G.edge t.node s.node ∧ t.dir = .fromChild) ∨
      (G.edge s.node t.node ∧ t.dir = .fromParent)
    )
  | .fromParent =>
    (s.node ∉ Z ∧ G.edge s.node t.node ∧ t.dir = .fromParent) ∨
    (s.node ∈ anc ∧ G.edge t.node s.node ∧ t.dir = .fromChild)

def bbReachable (G : DAG V) (Z : Finset V) (s t : BallState V) : Prop :=
  let anc := Finset.univ.filter (fun v => ∃ z ∈ Z, G.Reaches v z)
  Relation.ReflTransGen (bbNext G Z anc) s t


def incomingOfDir : BallDir → DAG.Incoming
  | .fromParent => .fwd
  | .fromChild  => .bwd

lemma not_blockedAux_imp_open (G : DAG V) (Z : Finset V) (inc : DAG.Incoming)
    {x y : V} (p : Walk G x y)
    (h : ¬ Walk.blockedAux (G := G) Z inc p) :
    Walk.Open Z p := by
  unfold Walk.Open Walk.Blocked
  cases p with
  | nil v => simp [Walk.blockedAux] at h ⊢
  | fwd e rest =>
    cases inc <;> simp [Walk.blockedAux] at h ⊢ <;> tauto
  | bwd e rest =>
    cases inc <;> simp [Walk.blockedAux] at h ⊢ <;> tauto

-- Kontrapositivt: om det finnes en bbReachable-sti, finnes en åpen Walk
-- Dette er kjernen i ekvivalensen
theorem bbReachable_imp_not_blocked (G : DAG V) (Z : Finset V) (x y : V)
    (d1 d2 : BallDir)
    (hreach : bbReachable G Z {node := x, dir := d1} {node := y, dir := d2}) :
    exists p : Walk G x y, Not (Walk.blockedAux (G := G) Z (incomingOfDir d1) p) := by
  unfold bbReachable at hreach
  apply Relation.ReflTransGen.head_induction_on
    (motive := fun s _ => exists p : Walk G s.node y,
      Not (Walk.blockedAux (G := G) Z (incomingOfDir s.dir) p))
    hreach
  · exact ⟨Walk.nil _, by cases d2 <;> simp [Walk.blockedAux, incomingOfDir]⟩
  · intro ⟨c_node, c_dir⟩ _ hstep _ ih
    obtain ⟨p_ih, hp_ih⟩ := ih
    cases c_dir with
    | fromChild =>
      obtain ⟨hxZ, hcase⟩ := hstep
      rcases hcase with ⟨hedge, hdir⟩ | ⟨hedge, hdir⟩
      · simp only [hdir, incomingOfDir] at hp_ih ⊢
        exact ⟨Walk.bwd hedge p_ih, by simp [Walk.blockedAux, hxZ, hp_ih]⟩
      · simp only [hdir, incomingOfDir] at hp_ih ⊢
        exact ⟨Walk.fwd hedge p_ih, by simp [Walk.blockedAux, hxZ, hp_ih]⟩
    | fromParent =>
      rcases hstep with ⟨hxZ, hedge, hdir⟩ | ⟨hxanc, hedge, hdir⟩
      · simp only [hdir, incomingOfDir] at hp_ih ⊢
        exact ⟨Walk.fwd hedge p_ih, by simp [Walk.blockedAux, hxZ, hp_ih]⟩
      · simp only [hdir, incomingOfDir] at hp_ih ⊢
        simp only [Finset.mem_filter] at hxanc
        obtain ⟨_, z, hzZ, hreach⟩ := hxanc
        exact ⟨Walk.bwd hedge p_ih, by
          simp only [Walk.blockedAux]
          intro h
          rcases h with h1 | h2
          · exact h1 z hzZ hreach
          · exact hp_ih h2⟩

theorem bbReachable_imp_open_walk (G : DAG V) (Z : Finset V) (x y : V)
    (d1 d2 : BallDir)
    (hreach : bbReachable G Z {node := x, dir := d1} {node := y, dir := d2}) :
    exists p : Walk G x y, Walk.Open Z p :=
  let ⟨p, hp⟩ := bbReachable_imp_not_blocked G Z x y d1 d2 hreach
  ⟨p, not_blockedAux_imp_open G Z (incomingOfDir d1) p hp⟩

-- Korollaret vi vil ha
theorem DSeparated_imp_not_bbReachable (G : DAG V) (Z : Finset V) (x y : V)
    (hsep : G.DSeparated Z x y) :
    ∀ d1 d2 : BallDir, ¬ bbReachable G Z ⟨x, d1⟩ ⟨y, d2⟩ := by
  intro d1 d2 hreach
  have ⟨p, hp⟩ := bbReachable_imp_open_walk G Z x y d1 d2 hreach
  exact hp (hsep p)

#check @bbReachable_imp_open_walk
