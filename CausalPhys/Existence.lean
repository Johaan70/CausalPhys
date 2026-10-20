/-
  CausalPhys.Existence — løsninger FINNES, ikke bare at det finnes høyst én.

    1. Rekursive modeller (`Recursive.exists_unique`): for alle eksogene verdier
       finnes nøyaktig én løsning. Løsningen bygges ved velfundert rekursjon på
       Simon-rangen, så resultatet gjelder også uendelige modeller som
       spindelvevmodellen. Følgelig har ETHVERT inngrep nøyaktig ett utfall
       (`Recursive.doI_exists_unique`).

    2. Kontraktive modeller (`exists_unique_of_contractive`): er mekanismene en
       vektet kontraksjon i de endogene variablene, finnes nøyaktig én løsning.
       Beviset bruker Banachs fikspunktteorem fra Mathlib, etter et variabelbytte
       som gjør den vektede normen til maksnormen.

    3. Markedet: med lesningen «etterspørsel → Q, tilbud → P» og b < e gir
       teorem 2 eksistens og entydighet (`Market.exists_unique_of_contraction`).
       Eksistens for alle b, e > 0 er bevist direkte i Economics.lean.
-/
import CausalPhys.BlockSolvability
import Mathlib.Topology.MetricSpace.Contracting

set_option linter.unusedSectionVars false

namespace CausalPhys
namespace SCM

/-! ## 1. Rekursive modeller -/

section Recursive

universe u
variable {V : Type} {α : Type u}

/-- Ett steg i den rekursive konstruksjonen: les foreldrene (lavere rang),
    ellers de eksogene verdiene. -/
def solF (M : SCM V α) (rank : V → ℕ) (u : V → α) (v : V)
    (rec : (w : V) → (measure rank).rel w v → α) : α :=
  match M.mech v with
  | none => u v
  | some m => m.f (fun w => if h : rank w < rank v then rec w h else u w)

/-- Løsningen, definert ved velfundert rekursjon på rangen. -/
noncomputable def sol (M : SCM V α) (rank : V → ℕ) (u : V → α) : V → α :=
  (measure rank).wf.fix (solF M rank u)

theorem sol_eq (M : SCM V α) (rank : V → ℕ) (u : V → α) (v : V) :
    sol M rank u v = solF M rank u v (fun w _ => sol M rank u w) :=
  (measure rank).wf.fix_eq _ v

/-- Rekursive modeller har en løsning for alle eksogene verdier. -/
theorem Recursive.solves_sol {M : SCM V α} {rank : V → ℕ} (hr : M.Recursive rank) (u : V → α) :
    M.Solves u (sol M rank u) := by
  intro v
  have h := sol_eq M rank u v
  cases hm : M.mech v with
  | none =>
    simp only [solF, hm] at h
    exact h
  | some m =>
    simp only [solF, hm] at h
    show sol M rank u v = m.f (sol M rank u)
    rw [h]
    apply m.local_
    intro p hp
    simp only [hr v m hm p hp, ↓reduceDIte]

/-- Eksistens og entydighet. -/
theorem Recursive.exists_unique {M : SCM V α} {rank : V → ℕ} (hr : M.Recursive rank) (u : V → α) :
    ∃! s, M.Solves u s :=
  ⟨sol M rank u, hr.solves_sol u, fun _ hs => hr.unique hs (hr.solves_sol u)⟩

variable [DecidableEq V]

/-- Ethvert inngrep i en rekursiv modell har nøyaktig ett utfall. -/
theorem Recursive.doI_exists_unique {M : SCM V α} {rank : V → ℕ} (hr : M.Recursive rank)
    (x : V) (c : α) (u : V → α) : ∃! s, (M.doI x c).Solves u s :=
  (hr.doI x c).exists_unique u

end Recursive

/-! ## 2. Kontraktive modeller: Banach -/

section Banach

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Erstatt de eksogene koordinatene med `u`. -/
def fixExo (M : SCM V ℝ) (u s : V → ℝ) : V → ℝ :=
  fun w => match M.mech w with
    | none => u w
    | some _ => s w

/-- Løsningsoperatoren: eksogene får `u`, endogene sin mekanisme. -/
def Fop (M : SCM V ℝ) (u : V → ℝ) (s : V → ℝ) : V → ℝ :=
  fun v => match M.mech v with
    | none => u v
    | some m => m.f (fixExo M u s)

/-- Vektet kontraksjon i de endogene variablene: stemmer de eksogene, og er
    alle forskjeller høyst μ_w·δ, er mekanismeforskjellene høyst K·μ_v·δ. -/
def GloballyContractive (M : SCM V ℝ) (μ : V → ℝ) (K : ℝ) : Prop :=
  ∀ s t : V → ℝ, ∀ δ : ℝ, 0 ≤ δ →
    (∀ w, M.mech w = none → s w = t w) →
    (∀ w, |s w - t w| ≤ μ w * δ) →
    ∀ v m, M.mech v = some m → |m.f s - m.f t| ≤ K * (μ v * δ)

theorem solves_of_fixed {M : SCM V ℝ} {u s : V → ℝ} (h : Fop M u s = s) : M.Solves u s := by
  have hfix : fixExo M u s = s := by
    funext w
    have hw := congrFun h w
    unfold fixExo
    unfold Fop at hw
    cases hm : M.mech w with
    | none => simp only [hm] at hw ⊢; exact hw
    | some _ => rfl
  intro v
  have hv := congrFun h v
  unfold Fop at hv
  cases hm : M.mech v with
  | none => simp only [hm] at hv; exact hv.symm
  | some m => simp only [hm, hfix] at hv; exact hv.symm

/-- Variabelbytte: x ↦ μ·x gjør den vektede normen til maksnormen. -/
noncomputable def Gop (M : SCM V ℝ) (u μ : V → ℝ) (x : V → ℝ) : V → ℝ :=
  fun v => Fop M u (fun w => μ w * x w) v / μ v

theorem Gop_lipschitz {M : SCM V ℝ} {u μ : V → ℝ} {K : ℝ} (hμ : ∀ v, 0 < μ v) (hK0 : 0 ≤ K)
    (hc : GloballyContractive M μ K) (x y : V → ℝ) :
    dist (Gop M u μ x) (Gop M u μ y) ≤ K * dist x y := by
  have hd := dist_nonneg (x := x) (y := y)
  rw [dist_pi_le_iff (mul_nonneg hK0 hd)]
  intro v
  have hμv := hμ v
  simp only [Gop, Real.dist_eq]
  rw [← sub_div, abs_div, abs_of_pos hμv, div_le_iff₀ hμv]
  unfold Fop
  cases hm : M.mech v with
  | none =>
    simp only [sub_self, abs_zero]
    positivity
  | some m =>
    simp only
    have := hc (fixExo M u fun w => μ w * x w) (fixExo M u fun w => μ w * y w) (dist x y) hd
      (fun w hw => by simp only [fixExo, hw])
      (fun w => by
        unfold fixExo
        cases hw : M.mech w with
        | none => simp only [sub_self, abs_zero]; exact mul_nonneg (hμ w).le hd
        | some _ =>
          simp only
          rw [← mul_sub, abs_mul, abs_of_pos (hμ w)]
          exact mul_le_mul_of_nonneg_left
            (by simpa [Real.dist_eq] using dist_le_pi_dist x y w) (hμ w).le)
      v m hm
    linarith [this]

/-- Kontraksjon ⇒ nøyaktig én løsning (Banach). -/
theorem exists_unique_of_contractive (M : SCM V ℝ) (μ : V → ℝ) (K : ℝ)
    (hμ : ∀ v, 0 < μ v) (hK0 : 0 ≤ K) (hK1 : K < 1) (hc : GloballyContractive M μ K)
    (u : V → ℝ) : ∃! s, M.Solves u s := by
  set K' : NNReal := ⟨K, hK0⟩
  have hcon : ContractingWith K' (Gop M u μ) := by
    refine ⟨by exact_mod_cast hK1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    exact Gop_lipschitz hμ hK0 hc x y
  set x := ContractingWith.fixedPoint (Gop M u μ) hcon
  have hx : Gop M u μ x = x := hcon.fixedPoint_isFixedPt
  have hs : Fop M u (fun w => μ w * x w) = fun w => μ w * x w := by
    funext v
    have := congrFun hx v
    simp only [Gop] at this
    rw [div_eq_iff (hμ v).ne'] at this
    rw [this, mul_comm]
  refine ⟨fun w => μ w * x w, solves_of_fixed hs, fun t ht => ?_⟩
  -- entydighet: t gir også et fikspunkt for Gop
  have hFt : Fop M u t = t := by
    funext v
    have := ht v
    unfold Fop
    cases hm : M.mech v with
    | none => simp only [hm] at this ⊢; exact this.symm
    | some m =>
      simp only [hm] at this ⊢
      have hfx : fixExo M u t = t := by
        funext w
        have hw := ht w
        unfold fixExo
        cases hm' : M.mech w with
        | none => simp only [hm'] at hw ⊢; exact hw.symm
        | some _ => rfl
      rw [hfx]; exact this.symm
  have hGt : Gop M u μ (fun w => t w / μ w) = fun w => t w / μ w := by
    funext v
    simp only [Gop]
    have : (fun w => μ w * (t w / μ w)) = t := by
      funext w; field_simp [(hμ w).ne']
    rw [this, hFt]
  have := hcon.fixedPoint_unique hGt
  funext w
  have hw : t w / μ w = x w := congrFun this w
  rw [← hw]
  field_simp [(hμ w).ne']

end Banach
end SCM

/-! ## 3. Markedet -/

namespace Market

variable (m : Market)

/-- Markedets mekanismer er en global vektet kontraksjon når b < e. -/
theorem globallyContractive :
    SCM.GloballyContractive m.scm (fun | .P => m.Kc / m.b | _ => 1) m.Kc := by
  intro s t δ _ hexo hblk v mm hm
  have hv : Market.rank v = 1 := by
    cases v <;> simp [scm] at hm <;> rfl
  exact m.contractive 1 s t δ
    (fun z hz => by
      cases z <;> simp [Market.rank] at hz <;> exact hexo _ rfl)
    (fun z _ => hblk z) v mm hv hm

/-- Eksistens og entydighet fra Banach (b < e). -/
theorem exists_unique_of_contraction (hbe : m.b < m.e) (u : MV → ℝ) :
    ∃! s, m.scm.Solves u s :=
  SCM.exists_unique_of_contractive m.scm _ m.Kc
    (fun v => by
      have := m.hb; have := m.he
      have hK : 0 < m.Kc := by unfold Kc; positivity
      cases v <;> simp only [] <;> positivity)
    (by have := m.hb; have := m.he; unfold Kc; positivity)
    ((m.Kc_lt_one_iff).2 hbe) m.globallyContractive u

end Market

/-! ## 4. Spindelvevmodellen (uendelig mange variabler) -/

namespace Cobweb

/-- Prisbanen finnes og er entydig for enhver startavling — og etter ethvert
    prisinngrep. -/
theorem exists_unique (cw : Cobweb) (u : CW → ℝ) : ∃! s, cw.scm.Solves u s :=
  cw.recursive.exists_unique u

theorem doP_exists_unique (cw : Cobweb) (k : ℕ) (c : ℝ) (u : CW → ℝ) :
    ∃! s, (cw.scm.doI (.P k) c).Solves u s :=
  cw.recursive.doI_exists_unique (.P k) c u

end Cobweb
end CausalPhys
