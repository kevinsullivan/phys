import ..phys_dimensions
import linear_algebra.affine_space.basic
import ...math.euclidnK.euclidnK_definitions
import ..scalar


open_locale affine

section foo 

universes u 

abbreviation geom1d_frame := fm scalar 1 LENGTH
abbreviation geom1d_space (f : geom1d_frame) := spc scalar f

def geom1d_std_frame : geom1d_frame := fm.base 1 LENGTH
def geom1d_std_space : geom1d_space geom1d_std_frame := mk_space (geom1d_std_frame)


structure position1d {f : geom1d_frame} (s : spc _ f ) extends point s
@[ext] lemma position1d.ext : ∀  {f : geom1d_frame} {s : geom1d_space f } (x y : position1d s),
    x.to_point = y.to_point → x = y :=
    begin
        intros f s x y e,
        cases x,
        cases y,
        simp *,
        have h₁ : ({to_point := x} : position1d s).to_point = x := rfl,
        simp [h₁] at e,
        exact e 
    end

def position1d.coords {f : geom1d_frame} {s : geom1d_space f } (t :position1d s) :=
    t.to_point.coords

@[simp]
def mk_position1d' {f : geom1d_frame} (s : geom1d_space f ) (p : point s) : position1d s := position1d.mk p  
@[simp]
def mk_position1d {f : geom1d_frame} (s : geom1d_space f ) (k : scalar) : position1d s := position1d.mk (mk_point s ⟨[k],rfl⟩) 

structure displacement1d {f : geom1d_frame} (s : geom1d_space f ) extends vectr s 
@[ext] lemma displacement1d.ext : ∀  {f : geom1d_frame} {s : geom1d_space f } (x y : displacement1d s),
    x.to_vectr = y.to_vectr → x = y :=
    begin
        intros f s x y e,
        cases x,
        cases y,
        simp *,
        have h₁ : ({to_vectr := x} : displacement1d s).to_vectr = x := rfl,
        simp [h₁] at e,
        exact e 
    end


def displacement1d.coords {f : geom1d_frame} {s : geom1d_space f } (d :displacement1d s) :=
    d.to_vectr.coords

@[simp]
def mk_displacement1d' {f : geom1d_frame} (s : geom1d_space f ) (v : vectr s) : displacement1d s := displacement1d.mk v
@[simp]
def mk_displacement1d  {f : geom1d_frame} (s : geom1d_space f ) (k : scalar) : displacement1d s := displacement1d.mk (mk_vectr s ⟨[k],rfl⟩) 

@[simp]
def mk_geom1d_frame {parent : geom1d_frame} {s : spc scalar parent} (p : position1d s) (v : displacement1d s)
    : geom1d_frame :=
    ((mk_frame p.to_point (vectr_basis.mk (λi, v.to_vectr) sorry sorry)) : geom1d_frame) --fm.deriv LENGTH (p.to_point.to_pt, v.to_vectr.to_vec) parent   -- TODO: make sure v ≠ 0

end foo

section bar 

/-
    *************************************
    Instantiate module scalar (vector scalar)
    *************************************
-/

namespace geom1d
variables {f : geom1d_frame} {s : geom1d_space f } 
@[simp]
def add_displacement1d_displacement1d (v1 v2 : displacement1d s) : displacement1d s := 
    mk_displacement1d' s (v1.to_vectr + v2.to_vectr)
@[simp]
def smul_displacement1d (k : scalar) (v : displacement1d s) : displacement1d s := 
    mk_displacement1d' s (k • v.to_vectr)
@[simp]
def neg_displacement1d (v : displacement1d s) : displacement1d s := 
    mk_displacement1d' s ((-1 : scalar) • v.to_vectr)
@[simp]
def sub_displacement1d_displacement1d (v1 v2 : displacement1d s) : displacement1d s :=    -- v1-v2
    add_displacement1d_displacement1d v1 (neg_displacement1d v2)

-- See unframed file for template for proving module

instance has_add_displacement1d : has_add (displacement1d s) := ⟨ add_displacement1d_displacement1d ⟩
lemma add_assoc_displacement1d : ∀ a b c : displacement1d s, a + b + c = a + (b + c) := begin
    intros,
    ext,
    dsimp only [has_add.add],
    dsimp only [add_displacement1d_displacement1d, has_add.add],
    dsimp only [add_vectr_vectr, has_add.add],
    dsimp only [add_vec_vec, mk_displacement1d', mk_vectr'],
    simp only [add_assoc],
end
instance add_semigroup_displacement1d : add_semigroup (displacement1d s) := ⟨ add_displacement1d_displacement1d, add_assoc_displacement1d⟩ 
@[simp]
def displacement1d_zero  := mk_displacement1d s 0
instance has_zero_displacement1d : has_zero (displacement1d s) := ⟨displacement1d_zero⟩

/-
Andrew 5/14 - broke this, fix someposition1d soon
-/
lemma zero_add_displacement1d : ∀ a : displacement1d s, 0 + a = a := 
begin
    intros,
    ext,
    dsimp only [has_zero.zero, has_add.add],
    dsimp only [add_displacement1d_displacement1d, displacement1d_zero, mk_displacement1d', mk_displacement1d, has_add.add],
    dsimp only [add_vectr_vectr, mk_vectr', mk_vectr, mk_vec_n, has_add.add],
    dsimp only [add_vec_vec, mk_vec, vector.nth],
    simp only [list.nth_le_singleton, zero_add],
end

lemma add_zero_displacement1d : ∀ a : displacement1d s, a + 0 = a := 
begin
    intros,
    ext,
    dsimp only [has_zero.zero, has_add.add],
    dsimp only [add_displacement1d_displacement1d, displacement1d_zero, mk_displacement1d', mk_displacement1d, has_add.add],
    dsimp only [add_vectr_vectr, mk_vectr', mk_vectr, mk_vec_n, has_add.add],
    dsimp only [add_vec_vec, mk_vec, vector.nth],
    simp only [list.nth_le_singleton, add_zero],
end

@[simp]
def nsmul_displacement1d : ℕ → (displacement1d s) → (displacement1d s) 
| nat.zero v := displacement1d_zero
--| 1 v := v
| (nat.succ n) v := (add_displacement1d_displacement1d) v (nsmul_displacement1d n v)

instance add_monoid_displacement1d : add_monoid (displacement1d s) := ⟨ 
    -- add_semigroup
    add_displacement1d_displacement1d, 
    add_assoc_displacement1d, 
    -- has_zero
    displacement1d_zero,
    -- new structure 
    @zero_add_displacement1d f s, 
    add_zero_displacement1d,
    nsmul_displacement1d
⟩

instance has_neg_displacement1d : has_neg (displacement1d s) := ⟨neg_displacement1d⟩
instance has_sub_displacement1d : has_sub (displacement1d s) := ⟨ sub_displacement1d_displacement1d⟩ 
lemma sub_eq_add_neg_displacement1d : ∀ a b : displacement1d s, a - b = a + -b := 
begin
    intros,ext,
    refl,
end 

instance sub_neg_monoid_displacement1d : sub_neg_monoid (displacement1d s) := 
{
    neg := neg_displacement1d ,
    ..(show add_monoid (displacement1d s), by apply_instance)
}

lemma add_left_neg_displacement1d : ∀ a : displacement1d s, -a + a = 0 := 
begin
    intros,
    ext,
    dsimp only [has_zero.zero, has_add.add, has_neg.neg],
    dsimp only [neg_displacement1d, has_scalar.smul],
    dsimp only [add_displacement1d_displacement1d, smul_vectr, has_add.add, has_scalar.smul],
    dsimp only [add_vectr_vectr, smul_vec, mk_displacement1d', mk_vectr', has_add.add],
    dsimp only [add_vec_vec],
    simp only [neg_mul_eq_neg_mul_symm, one_mul, mk_vectr, displacement1d_zero, mk_displacement1d, add_left_neg],
    dsimp only [mk_vec_n, mk_vec, vector.nth],
    simp only [list.nth_le_singleton],
end

instance : add_group (displacement1d s) := {
    add_left_neg := begin
        exact add_left_neg_displacement1d,
    end,
..(show sub_neg_monoid (displacement1d s), by apply_instance),

}

lemma add_comm_displacement1d : ∀ a b : displacement1d s, a + b = b + a :=
begin
    intros,
    ext,
    dsimp only [has_add.add],
    dsimp only [add_displacement1d_displacement1d, has_add.add],
    dsimp only [add_vectr_vectr, has_add.add],
    dsimp only [add_vec_vec, mk_displacement1d', mk_vectr'],
    simp only [add_comm],
end
instance add_comm_semigroup_displacement1d : add_comm_semigroup (displacement1d s) := ⟨
    -- add_semigroup
    add_displacement1d_displacement1d, 
    add_assoc_displacement1d,
    add_comm_displacement1d,
⟩

instance add_comm_monoid_displacement1d : add_comm_monoid (displacement1d s) := {
    add_comm := begin
        exact add_comm_displacement1d
    end, 
    ..(show add_monoid (displacement1d s), by apply_instance)
}

instance has_scalar_displacement1d : has_scalar scalar (displacement1d s) := ⟨
smul_displacement1d,
⟩

lemma one_smul_displacement1d : ∀ b : displacement1d s, (1 : scalar) • b = b := begin
    intros,
    ext,
    dsimp only [has_scalar.smul],
    dsimp only [smul_displacement1d, has_scalar.smul],
    dsimp only [smul_vectr, has_scalar.smul],
    dsimp only [smul_vec, mk_displacement1d', mk_vectr'],
    simp only [one_mul],
end
lemma mul_smul_displacement1d : ∀ (x y : scalar) (b : displacement1d s), (x * y) • b = x • y • b := 
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
end

instance mul_action_displacement1d : mul_action scalar (displacement1d s) := ⟨
one_smul_displacement1d,
mul_smul_displacement1d,
⟩ 

lemma smul_add_displacement1d : ∀(r : scalar) (x y : displacement1d s), r • (x + y) = r • x + r • y := begin
    intros,
    ext,
    dsimp only [has_scalar.smul, has_add.add],
    dsimp only [smul_displacement1d, add_displacement1d_displacement1d, has_scalar.smul, has_add.add],
    dsimp only [smul_vectr, add_vectr_vectr, has_scalar.smul, has_add.add],
    dsimp only [smul_vec, add_vec_vec, mk_displacement1d', mk_vectr'],
    simp only [distrib.left_distrib],
    refl,
end
lemma smul_zero_displacement1d : ∀(r : scalar), r • (0 : displacement1d s) = 0 := begin
    intros,
    ext,
    dsimp only [has_scalar.smul, has_zero.zero],
    dsimp only [smul_displacement1d, displacement1d_zero, has_scalar.smul],
    dsimp only [smul_vectr, has_scalar.smul],
    dsimp only [smul_vec, mk_displacement1d', mk_vectr', mk_displacement1d, mk_vectr, mk_vec_n, mk_vec, vector.nth],
    simp only [list.nth_le_singleton, mul_zero],
end
instance distrib_mul_action_K_displacement1d : distrib_mul_action scalar (displacement1d s) := ⟨
smul_add_displacement1d,
smul_zero_displacement1d,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_displacement1d : ∀ (a b : scalar) (x : displacement1d s), (a + b) • x = a • x + b • x := 
begin
  intros,
  ext,
  exact right_distrib _ _ _,
end
lemma zero_smul_displacement1d : ∀ (x : displacement1d s), (0 : scalar) • x = 0 := begin
    intros,
    ext,
    dsimp only [has_scalar.smul, has_zero.zero],
    dsimp only [smul_displacement1d, displacement1d_zero, has_scalar.smul],
    dsimp only [smul_vectr, has_scalar.smul],
    dsimp only [smul_vec, mk_displacement1d', mk_vectr', mk_displacement1d, mk_vectr, mk_vec_n, mk_vec, vector.nth],
    simp only [list.nth_le_singleton, mul_eq_zero],
    apply or.inl,
    refl,
end
instance module_K_displacement1d : module scalar (displacement1d s) := ⟨ add_smul_displacement1d, zero_smul_displacement1d ⟩ 

instance add_comm_group_displacement1d : add_comm_group (displacement1d s) := {
    add_comm := begin
        exact add_comm_displacement1d
        
        /-intros,
        ext,
        let h0 : (a + b).to_vec = a.to_vec + b.to_vec := rfl,
        let h1 : (b + a).to_vec = b.to_vec + a.to_vec := rfl,
        rw [h0,h1],
        exact add_comm _ _,
        exact add_comm _ _,-/
    end,
--to_add_group := (show add_group (vec K), by apply_instance),
--to_add_comm_monoid := (show add_comm_monoid (vec K), by apply_instance),
..(show add_group (displacement1d s), by apply_instance)
}
instance : module scalar (displacement1d s) := @geom1d.module_K_displacement1d f s


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
instance : has_add (displacement1d s) := ⟨add_displacement1d_displacement1d⟩
instance : has_zero (displacement1d s) := ⟨displacement1d_zero⟩
instance : has_neg (displacement1d s) := ⟨neg_displacement1d⟩

@[simp]
def sub_position1d_position1d {f : geom1d_frame} {s : geom1d_space f } (p1 p2 : position1d s) : displacement1d s := 
    mk_displacement1d' s (p1.to_point -ᵥ p2.to_point)
@[simp]
def add_position1d_displacement1d {f : geom1d_frame} {s : geom1d_space f } (p : position1d s) (v : displacement1d s) : position1d s := 
    mk_position1d' s (v.to_vectr +ᵥ p.to_point) -- reorder assumes order is irrelevant
@[simp]
def add_displacement1d_position1d {f : geom1d_frame} {s : geom1d_space f } (v : displacement1d s) (p : position1d s) : position1d s := 
    mk_position1d' s (v.to_vectr +ᵥ p.to_point)
    
instance : has_vadd (displacement1d s) (position1d s) := ⟨add_displacement1d_position1d⟩

lemma zero_displacement1d_vadd'_a1 : ∀ p : position1d s, (0 : displacement1d s) +ᵥ p = p := begin
    intros,
    ext,
    dsimp only [has_vadd.vadd, has_zero.zero],
    dsimp only [add_displacement1d_position1d, displacement1d_zero, has_vadd.vadd],
    dsimp only [add_vectr_point, has_vadd.vadd],
    dsimp only [aff_vec_group_action, add_vec_pt, mk_position1d', mk_point', mk_displacement1d, mk_vectr, mk_vec_n, mk_vec, vector.nth],
    simp only [list.nth_le_singleton, add_zero],
end
lemma displacement1d_add_assoc'_a1 : ∀ (g1 g2 : displacement1d s) (p : position1d s), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := begin
    intros,
    ext,
    dsimp only [has_add.add, has_vadd.vadd],
    dsimp only [add_displacement1d_position1d, add_displacement1d_displacement1d, has_add.add, has_vadd.vadd],
    dsimp only [add_vectr_point, add_vectr_vectr, has_add.add, has_vadd.vadd],
    dsimp only [aff_vec_group_action, add_vec_vec, add_vec_pt, mk_position1d', mk_point', mk_displacement1d', mk_vectr'],
    simp only [add_assoc, add_right_inj],
    simp only [add_comm],
end


instance displacement1d_add_action: add_action (displacement1d s) (position1d s) := 
⟨ zero_displacement1d_vadd'_a1, 
begin
    let h0 := displacement1d_add_assoc'_a1,
    intros,
    exact (h0 g₁ g₂ p).symm
end⟩ 

instance position1d_has_vsub : has_vsub (displacement1d s) (position1d s) := ⟨ sub_position1d_position1d⟩ 

instance : nonempty (position1d s) := ⟨mk_position1d s 0⟩

lemma position1d_vsub_vadd_a1 : ∀ (p1 p2 : (position1d s)), (p1 -ᵥ p2) +ᵥ p2 = p1 := begin
    intros,
    ext,
    dsimp only [has_vsub.vsub, has_vadd.vadd],
    dsimp only [add_displacement1d_position1d, sub_position1d_position1d, has_vsub.vsub, has_vadd.vadd],
    dsimp only [add_vectr_point, aff_point_group_sub, sub_point_point, has_vsub.vsub, has_vadd.vadd],
    dsimp only [aff_vec_group_action, aff_point_group_sub, add_vec_pt, aff_pt_group_sub, sub_pt_pt, mk_position1d', mk_point', mk_displacement1d', mk_vectr'],
    simp only [add_sub_cancel'_right],
end
lemma position1d_vadd_vsub_a1 : ∀ (g : displacement1d s) (p : position1d s), g +ᵥ p -ᵥ p = g := 
begin
    intros, ext,
    repeat {
    have h0 : ((g +ᵥ p -ᵥ p) : displacement1d s).to_vectr = (g.to_vectr +ᵥ p.to_point -ᵥ p.to_point) := rfl,
    rw h0,
    simp *,
    }
    
end

instance aff_geom1d_torsor : add_torsor (displacement1d s) (position1d s) := 
⟨ 
    begin
        exact position1d_vsub_vadd_a1,
    end,
    begin
        exact position1d_vadd_vsub_a1,
    end,
⟩

open_locale affine

instance : affine_space (displacement1d s) (position1d s) := @geom1d.aff_geom1d_torsor f s

end geom1d -- ha ha
end bar

/-
Newer version
Tradeoff - Does not directly extend from affine equiv. Base class is an equiv on points and vectrs

Extension methods are provided to directly transform Times and Duration between frames
-/
@[ext]
structure geom1d_transform {f1 : geom1d_frame} {f2 : geom1d_frame} (sp1 : geom1d_space f1) (sp2 : geom1d_space f2)
  extends fm_tr sp1 sp2

def geom1d_space.mk_geom1d_transform_to {f1 : geom1d_frame} (s1 : geom1d_space f1) : Π {f2 : geom1d_frame} (s2 : geom1d_space f2), 
        geom1d_transform s1 s2 := --(position1d s2) ≃ᵃ[scalar] (position1d s1) := 
    λ f2 s2,
        ⟨s1.fm_tr s2⟩

def geom1d_transform.symm 
    {f1 : geom1d_frame} {f2 : geom1d_frame} {sp1 : geom1d_space f1} {sp2 : geom1d_space f2} (ttr : geom1d_transform sp1 sp2)
    : geom1d_transform sp2 sp1 := ⟨(ttr.1).symm⟩


def geom1d_transform.trans 
    {f1 : geom1d_frame} {f2 : geom1d_frame} {f3 : geom1d_frame} {sp1 : geom1d_space f1} {sp2 : geom1d_space f2} {sp3 : geom1d_space f3} 
    (ttr : geom1d_transform sp1 sp2)
    : geom1d_transform sp2 sp3 → geom1d_transform sp1 sp3 := λttr_, ⟨(ttr.1).trans ttr_.1⟩

def geom1d_transform.transform_position1d
    {f1 : geom1d_frame} {s1 : spc _ f1}
    {f2 : geom1d_frame} {s2 : spc _ f2}
    (tr: geom1d_transform s1 s2 ) : position1d s1 → position1d s2 :=
    λt : position1d s1,
    ⟨tr.to_fm_tr.to_equiv t.to_point⟩

def geom1d_transform.transform_displacement1d
    {f1 : geom1d_frame} {s1 : spc _ f1}
    {f2 : geom1d_frame} {s2 : spc _ f2}
    (tr: geom1d_transform s1 s2 ) : displacement1d s1 → displacement1d s2 :=
    λd,
    let as_pt : point s1 := ⟨λi, mk_pt scalar (d.coords i).coord⟩ in
    let tr_pt := (tr.to_equiv as_pt) in
    ⟨⟨λi, mk_vec scalar (tr_pt.coords i).coord⟩⟩
