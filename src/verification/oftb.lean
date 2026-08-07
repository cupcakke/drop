variable {F : Type}

def succ_not_zero (n : Nat) (h : Nat.succ n = 0) : False :=
  nomatch h

def zero_not_succ (n : Nat) (h : 0 = Nat.succ n) : False :=
  nomatch h

def succ_inj {n m : Nat} (h : Nat.succ n = Nat.succ m) : n = m :=
  congrArg (fun x => match x with | 0 => 0 | Nat.succ k => k) h

def nat_zero_add : (m : Nat) → 0 + m = m
| 0 => Eq.refl 0
| Nat.succ m => congrArg Nat.succ (nat_zero_add m)

def nat_succ_add (n : Nat) : (m : Nat) → Nat.succ n + m = Nat.succ (n + m)
| 0 => Eq.refl (Nat.succ n)
| Nat.succ m => congrArg Nat.succ (nat_succ_add n m)

def congr_cons {α : Type} {x y : α} {xs ys : List α} (hx : x = y) (hxs : xs = ys) : x :: xs = y :: ys :=
  match hx, hxs with
  | Eq.refl _, Eq.refl _ => Eq.refl _

def congr_append {α : Type} {xs ys us vs : List α} (h1 : xs = ys) (h2 : us = vs) : xs ++ us = ys ++ vs :=
  match h1, h2 with
  | Eq.refl _, Eq.refl _ => Eq.refl _

def congr_add {n1 n2 m1 m2 : Nat} (h1 : n1 = n2) (h2 : m1 = m2) : n1 + m1 = n2 + m2 :=
  match h1, h2 with
  | Eq.refl _, Eq.refl _ => Eq.refl _

def split_at (n : Nat) (L : List F) : List F × List F :=
  match n with
  | 0 => ([], L)
  | Nat.succ k =>
    match L with
    | [] => ([], [])
    | x :: xs =>
      let (l1, l2) := split_at k xs
      (x :: l1, l2)

theorem split_at_lengths_gen : (n m : Nat) → (L : List F) → L.length = n + m →
  (split_at n L).1.length = n ∧ (split_at n L).2.length = m
| 0, m, L, h =>
  ⟨Eq.refl 0, Eq.trans h (nat_zero_add m)⟩
| Nat.succ n, m, [], h =>
  False.elim (zero_not_succ (n + m) (Eq.trans h (nat_succ_add n m)))
| Nat.succ n, m, _ :: xs, h =>
  let h' : Nat.succ xs.length = Nat.succ (n + m) := Eq.trans h (nat_succ_add n m)
  let h_len : xs.length = n + m := succ_inj h'
  let rec_res := split_at_lengths_gen n m xs h_len
  ⟨congrArg Nat.succ rec_res.left, rec_res.right⟩

theorem split_at_reconstruct : (n : Nat) → (L : List F) →
  (split_at n L).1 ++ (split_at n L).2 = L
| 0, L => Eq.refl L
| Nat.succ _, [] => Eq.refl []
| Nat.succ n, x :: xs =>
  let rec_res := split_at_reconstruct n xs
  congrArg (List.cons x) rec_res

theorem split_at_append : (n : Nat) → (L1 L2 : List F) → L1.length = n →
  split_at n (L1 ++ L2) = (L1, L2)
| 0, [], L2, _ => Eq.refl ([], L2)
| 0, _ :: _, _, h => False.elim (succ_not_zero _ h)
| Nat.succ n, x :: xs, L2, h =>
  let h_rec := split_at_append n xs L2 (succ_inj h)
  congrArg (fun p => (x :: p.1, p.2)) h_rec
| Nat.succ _, [], _, h => False.elim (zero_not_succ _ h)

theorem length_zipWith : (f : F → F → F) → (L1 L2 : List F) → L1.length = L2.length →
  (List.zipWith f L1 L2).length = L1.length
| _, [], [], _ => Eq.refl 0
| f, _ :: xs, _ :: ys, h =>
  let h_len : xs.length = ys.length := succ_inj h
  congrArg Nat.succ (length_zipWith f xs ys h_len)
| _, _ :: _, [], h => False.elim (succ_not_zero _ h)
| _, [], _ :: _, h => False.elim (zero_not_succ _ h)

theorem length_append : (L1 L2 : List F) → (L1 ++ L2).length = L1.length + L2.length
| [], L2 => Eq.symm (nat_zero_add L2.length)
| _ :: xs, L2 =>
  Eq.trans (congrArg Nat.succ (length_append xs L2)) (Eq.symm (nat_succ_add xs.length L2.length))

structure ScaleAlgebra (F : Type) where
  add : F → F → F
  sub : F → F → F
  mul : F → F → F
  scale : F
  two : F
  one : F
  distrib_add : ∀ x y z : F, add (mul x z) (mul y z) = mul (add x y) z
  distrib_sub : ∀ x y z : F, sub (mul x z) (mul y z) = mul (sub x y) z
  mul_comm : ∀ x y : F, mul x y = mul y x
  mul_assoc : ∀ x y z : F, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : F, mul x one = x
  add_sub_add : ∀ a b : F, add (sub a b) (add a b) = mul two a
  add_sub_sub : ∀ a b : F, sub (add a b) (sub a b) = mul two b
  sub_add_sub_rev : ∀ u v : F, sub (add u v) (sub v u) = mul two u
  add_add_sub_rev : ∀ u v : F, add (add u v) (sub v u) = mul two v
  scale_property : mul (mul two scale) scale = one

def first_component_proof (sa : ScaleAlgebra F) (a b : F) :
  sa.mul (sa.add (sa.mul (sa.sub a b) sa.scale) (sa.mul (sa.add a b) sa.scale)) sa.scale = a :=
  let step1 : sa.add (sa.mul (sa.sub a b) sa.scale) (sa.mul (sa.add a b) sa.scale) = sa.mul (sa.add (sa.sub a b) (sa.add a b)) sa.scale :=
    sa.distrib_add (sa.sub a b) (sa.add a b) sa.scale
  let step2 : sa.add (sa.sub a b) (sa.add a b) = sa.mul sa.two a :=
    sa.add_sub_add a b
  let step3 : sa.mul (sa.add (sa.sub a b) (sa.add a b)) sa.scale = sa.mul (sa.mul sa.two a) sa.scale :=
    congrArg (fun x => sa.mul x sa.scale) step2
  let step4 : sa.add (sa.mul (sa.sub a b) sa.scale) (sa.mul (sa.add a b) sa.scale) = sa.mul (sa.mul sa.two a) sa.scale :=
    Eq.trans step1 step3
  let step5 : sa.mul (sa.add (sa.mul (sa.sub a b) sa.scale) (sa.mul (sa.add a b) sa.scale)) sa.scale = sa.mul (sa.mul (sa.mul sa.two a) sa.scale) sa.scale :=
    congrArg (fun x => sa.mul x sa.scale) step4
  let s1 : sa.mul (sa.mul (sa.mul sa.two a) sa.scale) sa.scale = sa.mul (sa.mul (sa.mul a sa.two) sa.scale) sa.scale :=
    congrArg (fun x => sa.mul (sa.mul x sa.scale) sa.scale) (sa.mul_comm sa.two a)
  let s2 : sa.mul (sa.mul (sa.mul a sa.two) sa.scale) sa.scale = sa.mul (sa.mul a (sa.mul sa.two sa.scale)) sa.scale :=
    congrArg (fun x => sa.mul x sa.scale) (sa.mul_assoc a sa.two sa.scale)
  let s3 : sa.mul (sa.mul a (sa.mul sa.two sa.scale)) sa.scale = sa.mul a (sa.mul (sa.mul sa.two sa.scale) sa.scale) :=
    sa.mul_assoc a (sa.mul sa.two sa.scale) sa.scale
  let s4 : sa.mul a (sa.mul (sa.mul sa.two sa.scale) sa.scale) = sa.mul a sa.one :=
    congrArg (sa.mul a) sa.scale_property
  let s5 : sa.mul a sa.one = a :=
    sa.mul_one a
  let s_tot : sa.mul (sa.mul (sa.mul sa.two a) sa.scale) sa.scale = a :=
    Eq.trans s1 (Eq.trans s2 (Eq.trans s3 (Eq.trans s4 s5)))
  Eq.trans step5 s_tot

def second_component_proof (sa : ScaleAlgebra F) (a b : F) :
  sa.mul (sa.sub (sa.mul (sa.add a b) sa.scale) (sa.mul (sa.sub a b) sa.scale)) sa.scale = b :=
  let step1 : sa.sub (sa.mul (sa.add a b) sa.scale) (sa.mul (sa.sub a b) sa.scale) = sa.mul (sa.sub (sa.add a b) (sa.sub a b)) sa.scale :=
    sa.distrib_sub (sa.add a b) (sa.sub a b) sa.scale
  let step2 : sa.sub (sa.add a b) (sa.sub a b) = sa.mul sa.two b :=
    sa.add_sub_sub a b
  let step3 : sa.mul (sa.sub (sa.add a b) (sa.sub a b)) sa.scale = sa.mul (sa.mul sa.two b) sa.scale :=
    congrArg (fun x => sa.mul x sa.scale) step2
  let step4 : sa.sub (sa.mul (sa.add a b) sa.scale) (sa.mul (sa.sub a b) sa.scale) = sa.mul (sa.mul sa.two b) sa.scale :=
    Eq.trans step1 step3
  let step5 : sa.mul (sa.sub (sa.mul (sa.add a b) sa.scale) (sa.mul (sa.sub a b) sa.scale)) sa.scale = sa.mul (sa.mul (sa.mul sa.two b) sa.scale) sa.scale :=
    congrArg (fun x => sa.mul x sa.scale) step4
  let s1 : sa.mul (sa.mul (sa.mul sa.two b) sa.scale) sa.scale = sa.mul (sa.mul (sa.mul b sa.two) sa.scale) sa.scale :=
    congrArg (fun x => sa.mul (sa.mul x sa.scale) sa.scale) (sa.mul_comm sa.two b)
  let s2 : sa.mul (sa.mul (sa.mul b sa.two) sa.scale) sa.scale = sa.mul (sa.mul b (sa.mul sa.two sa.scale)) sa.scale :=
    congrArg (fun x => sa.mul x sa.scale) (sa.mul_assoc b sa.two sa.scale)
  let s3 : sa.mul (sa.mul b (sa.mul sa.two sa.scale)) sa.scale = sa.mul b (sa.mul (sa.mul sa.two sa.scale) sa.scale) :=
    sa.mul_assoc b (sa.mul sa.two sa.scale) sa.scale
  let s4 : sa.mul b (sa.mul (sa.mul sa.two sa.scale) sa.scale) = sa.mul b sa.one :=
    congrArg (sa.mul b) sa.scale_property
  let s5 : sa.mul b sa.one = b :=
    sa.mul_one b
  let s_tot : sa.mul (sa.mul (sa.mul sa.two b) sa.scale) sa.scale = b :=
    Eq.trans s1 (Eq.trans s2 (Eq.trans s3 (Eq.trans s4 s5)))
  Eq.trans step5 s_tot

def first_component_proof_rev (sa : ScaleAlgebra F) (u v : F) :
  sa.mul (sa.sub (sa.mul (sa.add u v) sa.scale) (sa.mul (sa.sub v u) sa.scale)) sa.scale = u :=
  let step1 : sa.sub (sa.mul (sa.add u v) sa.scale) (sa.mul (sa.sub v u) sa.scale) = sa.mul (sa.sub (sa.add u v) (sa.sub v u)) sa.scale :=
    sa.distrib_sub (sa.add u v) (sa.sub v u) sa.scale
  let step2 : sa.sub (sa.add u v) (sa.sub v u) = sa.mul sa.two u :=
    sa.sub_add_sub_rev u v
  let step3 : sa.mul (sa.sub (sa.add u v) (sa.sub v u)) sa.scale = sa.mul (sa.mul sa.two u) sa.scale :=
    congrArg (fun x => sa.mul x sa.scale) step2
  let step4 : sa.sub (sa.mul (sa.add u v) sa.scale) (sa.mul (sa.sub v u) sa.scale) = sa.mul (sa.mul sa.two u) sa.scale :=
    Eq.trans step1 step3
  let step5 : sa.mul (sa.sub (sa.mul (sa.add u v) sa.scale) (sa.mul (sa.sub v u) sa.scale)) sa.scale = sa.mul (sa.mul (sa.mul sa.two u) sa.scale) sa.scale :=
    congrArg (fun x => sa.mul x sa.scale) step4
  let s1 : sa.mul (sa.mul (sa.mul sa.two u) sa.scale) sa.scale = sa.mul (sa.mul (sa.mul u sa.two) sa.scale) sa.scale :=
    congrArg (fun x => sa.mul (sa.mul x sa.scale) sa.scale) (sa.mul_comm sa.two u)
  let s2 : sa.mul (sa.mul (sa.mul u sa.two) sa.scale) sa.scale = sa.mul (sa.mul u (sa.mul sa.two sa.scale)) sa.scale :=
    congrArg (fun x => sa.mul x sa.scale) (sa.mul_assoc u sa.two sa.scale)
  let s3 : sa.mul (sa.mul u (sa.mul sa.two sa.scale)) sa.scale = sa.mul u (sa.mul (sa.mul sa.two sa.scale) sa.scale) :=
    sa.mul_assoc u (sa.mul sa.two sa.scale) sa.scale
  let s4 : sa.mul u (sa.mul (sa.mul sa.two sa.scale) sa.scale) = sa.mul u sa.one :=
    congrArg (sa.mul u) sa.scale_property
  let s5 : sa.mul u sa.one = u :=
    sa.mul_one u
  let s_tot : sa.mul (sa.mul (sa.mul sa.two u) sa.scale) sa.scale = u :=
    Eq.trans s1 (Eq.trans s2 (Eq.trans s3 (Eq.trans s4 s5)))
  Eq.trans step5 s_tot

def second_component_proof_rev (sa : ScaleAlgebra F) (u v : F) :
  sa.mul (sa.add (sa.mul (sa.add u v) sa.scale) (sa.mul (sa.sub v u) sa.scale)) sa.scale = v :=
  let step1 : sa.add (sa.mul (sa.add u v) sa.scale) (sa.mul (sa.sub v u) sa.scale) = sa.mul (sa.add (sa.add u v) (sa.sub v u)) sa.scale :=
    sa.distrib_add (sa.add u v) (sa.sub v u) sa.scale
  let step2 : sa.add (sa.add u v) (sa.sub v u) = sa.mul sa.two v :=
    sa.add_add_sub_rev u v
  let step3 : sa.mul (sa.add (sa.add u v) (sa.sub v u)) sa.scale = sa.mul (sa.mul sa.two v) sa.scale :=
    congrArg (fun x => sa.mul x sa.scale) step2
  let step4 : sa.add (sa.mul (sa.add u v) sa.scale) (sa.mul (sa.sub v u) sa.scale) = sa.mul (sa.mul sa.two v) sa.scale :=
    Eq.trans step1 step3
  let step5 : sa.mul (sa.add (sa.mul (sa.add u v) sa.scale) (sa.mul (sa.sub v u) sa.scale)) sa.scale = sa.mul (sa.mul (sa.mul sa.two v) sa.scale) sa.scale :=
    congrArg (fun x => sa.mul x sa.scale) step4
  let s1 : sa.mul (sa.mul (sa.mul sa.two v) sa.scale) sa.scale = sa.mul (sa.mul (sa.mul v sa.two) sa.scale) sa.scale :=
    congrArg (fun x => sa.mul (sa.mul x sa.scale) sa.scale) (sa.mul_comm sa.two v)
  let s2 : sa.mul (sa.mul (sa.mul v sa.two) sa.scale) sa.scale = sa.mul (sa.mul v (sa.mul sa.two sa.scale)) sa.scale :=
    congrArg (fun x => sa.mul x sa.scale) (sa.mul_assoc v sa.two sa.scale)
  let s3 : sa.mul (sa.mul v (sa.mul sa.two sa.scale)) sa.scale = sa.mul v (sa.mul (sa.mul sa.two sa.scale) sa.scale) :=
    sa.mul_assoc v (sa.mul sa.two sa.scale) sa.scale
  let s4 : sa.mul v (sa.mul (sa.mul sa.two sa.scale) sa.scale) = sa.mul v sa.one :=
    congrArg (sa.mul v) sa.scale_property
  let s5 : sa.mul v sa.one = v :=
    sa.mul_one v
  let s_tot : sa.mul (sa.mul (sa.mul sa.two v) sa.scale) sa.scale = v :=
    Eq.trans s1 (Eq.trans s2 (Eq.trans s3 (Eq.trans s4 s5)))
  Eq.trans step5 s_tot

def prove_inverse_pair (sa : ScaleAlgebra F) (a b : F) :
  let u := sa.mul (sa.sub a b) sa.scale
  let v := sa.mul (sa.add a b) sa.scale
  sa.mul (sa.add u v) sa.scale = a ∧ sa.mul (sa.sub v u) sa.scale = b :=
  ⟨first_component_proof sa a b, second_component_proof sa a b⟩

def prove_inverse_pair_rev (sa : ScaleAlgebra F) (u v : F) :
  let a := sa.mul (sa.add u v) sa.scale
  let b := sa.mul (sa.sub v u) sa.scale
  sa.mul (sa.sub a b) sa.scale = u ∧ sa.mul (sa.add a b) sa.scale = v :=
  ⟨first_component_proof_rev sa u v, second_component_proof_rev sa u v⟩

def zipWith_inverse_list (sa : ScaleAlgebra F) :
  (L1 L2 : List F) → L1.length = L2.length →
  List.zipWith (fun x y => sa.mul (sa.add x y) sa.scale)
    (List.zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) L1 L2)
    (List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) L1 L2) = L1 ∧
  List.zipWith (fun x y => sa.mul (sa.sub y x) sa.scale)
    (List.zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) L1 L2)
    (List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) L1 L2) = L2
| [], [], _ => ⟨Eq.refl [], Eq.refl []⟩
| a :: as, b :: bs, h =>
  let h_len : as.length = bs.length := succ_inj h
  let rec_res := zipWith_inverse_list sa as bs h_len
  let pair_res := prove_inverse_pair sa a b
  ⟨congr_cons pair_res.left rec_res.left,
   congr_cons pair_res.right rec_res.right⟩
| _ :: _, [], h => False.elim (succ_not_zero _ h)
| [], _ :: _, h => False.elim (zero_not_succ _ h)

def zipWith_inverse_list_rev (sa : ScaleAlgebra F) :
  (L1 L2 : List F) → L1.length = L2.length →
  List.zipWith (fun x y => sa.mul (sa.sub x y) sa.scale)
    (List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) L1 L2)
    (List.zipWith (fun a b => sa.mul (sa.sub b a) sa.scale) L1 L2) = L1 ∧
  List.zipWith (fun x y => sa.mul (sa.add x y) sa.scale)
    (List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) L1 L2)
    (List.zipWith (fun a b => sa.mul (sa.sub b a) sa.scale) L1 L2) = L2
| [], [], _ => ⟨Eq.refl [], Eq.refl []⟩
| u :: us, v :: vs, h =>
  let h_len : us.length = vs.length := succ_inj h
  let rec_res := zipWith_inverse_list_rev sa us vs h_len
  let pair_res := prove_inverse_pair_rev sa u v
  ⟨congr_cons pair_res.left rec_res.left,
   congr_cons pair_res.right rec_res.right⟩
| _ :: _, [], h => False.elim (succ_not_zero _ h)
| [], _ :: _, h => False.elim (zero_not_succ _ h)

def forwardCore (sa : ScaleAlgebra F) (dim : Nat) (L : List F) : List F :=
  let x1 := (split_at dim L).1
  let x2 := (split_at dim L).2
  let x1_new := List.zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) x1 x2
  let x2_new := List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) x1 x2
  x1_new ++ x2_new

def backwardCore (sa : ScaleAlgebra F) (dim : Nat) (L : List F) : List F :=
  let g1 := (split_at dim L).1
  let g2 := (split_at dim L).2
  let g1_new := List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) g1 g2
  let g2_new := List.zipWith (fun a b => sa.mul (sa.sub b a) sa.scale) g1 g2
  g1_new ++ g2_new

theorem oftb_invertible (sa : ScaleAlgebra F) (dim : Nat) (L : List F) (h : L.length = dim + dim) :
  backwardCore sa dim (forwardCore sa dim L) = L :=
  let x1 := (split_at dim L).1
  let x2 := (split_at dim L).2
  let h_splits : x1.length = dim ∧ x2.length = dim := split_at_lengths_gen dim dim L h
  let x1_new := List.zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) x1 x2
  let x2_new := List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) x1 x2
  let h_x1_new_len : x1_new.length = dim :=
    Eq.trans (length_zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) x1 x2 (Eq.trans h_splits.left (Eq.symm h_splits.right))) h_splits.left
  let h_split_new : split_at dim (x1_new ++ x2_new) = (x1_new, x2_new) :=
    split_at_append dim x1_new x2_new h_x1_new_len
  let h_zip_len : x1.length = x2.length := Eq.trans h_splits.left (Eq.symm h_splits.right)
  let inv_res := zipWith_inverse_list sa x1 x2 h_zip_len
  let h_g1_new : List.zipWith (fun x y => sa.mul (sa.add x y) sa.scale) x1_new x2_new = x1 := inv_res.left
  let h_g2_new : List.zipWith (fun x y => sa.mul (sa.sub y x) sa.scale) x1_new x2_new = x2 := inv_res.right
  let step1 : backwardCore sa dim (forwardCore sa dim L) =
    let (g1, g2) := split_at dim (x1_new ++ x2_new);
    List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) g1 g2 ++
    List.zipWith (fun a b => sa.mul (sa.sub b a) sa.scale) g1 g2 := Eq.refl _
  let step2 : (let (g1, g2) := split_at dim (x1_new ++ x2_new);
    List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) g1 g2 ++
    List.zipWith (fun a b => sa.mul (sa.sub b a) sa.scale) g1 g2) =
    (List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) x1_new x2_new ++
     List.zipWith (fun a b => sa.mul (sa.sub b a) sa.scale) x1_new x2_new) :=
    congrArg (fun p =>
      List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) p.1 p.2 ++
      List.zipWith (fun a b => sa.mul (sa.sub b a) sa.scale) p.1 p.2) h_split_new
  let step3 : (List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) x1_new x2_new ++
     List.zipWith (fun a b => sa.mul (sa.sub b a) sa.scale) x1_new x2_new) =
    x1 ++ x2 :=
    congr_append h_g1_new h_g2_new
  let step4 : x1 ++ x2 = L := split_at_reconstruct dim L
  Eq.trans step1 (Eq.trans step2 (Eq.trans step3 step4))

theorem oftb_invertible_rev (sa : ScaleAlgebra F) (dim : Nat) (L : List F) (h : L.length = dim + dim) :
  forwardCore sa dim (backwardCore sa dim L) = L :=
  let g1 := (split_at dim L).1
  let g2 := (split_at dim L).2
  let h_splits : g1.length = dim ∧ g2.length = dim := split_at_lengths_gen dim dim L h
  let g1_new := List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) g1 g2
  let g2_new := List.zipWith (fun a b => sa.mul (sa.sub b a) sa.scale) g1 g2
  let h_g1_new_len : g1_new.length = dim :=
    Eq.trans (length_zipWith (fun a b => sa.mul (sa.add a b) sa.scale) g1 g2 (Eq.trans h_splits.left (Eq.symm h_splits.right))) h_splits.left
  let h_split_new : split_at dim (g1_new ++ g2_new) = (g1_new, g2_new) :=
    split_at_append dim g1_new g2_new h_g1_new_len
  let h_zip_len : g1.length = g2.length := Eq.trans h_splits.left (Eq.symm h_splits.right)
  let inv_res := zipWith_inverse_list_rev sa g1 g2 h_zip_len
  let h_x1_new : List.zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) g1_new g2_new = g1 := inv_res.left
  let h_x2_new : List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) g1_new g2_new = g2 := inv_res.right
  let step1 : forwardCore sa dim (backwardCore sa dim L) =
    let (x1, x2) := split_at dim (g1_new ++ g2_new);
    List.zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) x1 x2 ++
    List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) x1 x2 := Eq.refl _
  let step2 : (let (x1, x2) := split_at dim (g1_new ++ g2_new);
    List.zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) x1 x2 ++
    List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) x1 x2) =
    (List.zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) g1_new g2_new ++
     List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) g1_new g2_new) :=
    congrArg (fun p =>
      List.zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) p.1 p.2 ++
      List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) p.1 p.2) h_split_new
  let step3 : (List.zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) g1_new g2_new ++
     List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) g1_new g2_new) =
    g1 ++ g2 :=
    congr_append h_x1_new h_x2_new
  let step4 : g1 ++ g2 = L := split_at_reconstruct dim L
  Eq.trans step1 (Eq.trans step2 (Eq.trans step3 step4))

def ValidShape : List Nat → Prop
| [] => False
| [x] => x > 0
| x :: xs => x > 0 ∧ ValidShape xs

def shapeProd : List Nat → Nat
| [] => 1
| x :: xs => x * shapeProd xs

structure Tensor (F : Type) where
  shape : List Nat
  data : List F
  h_valid : ValidShape shape
  h_len : data.length = shapeProd shape

def init_tensor_spec (F : Type) (shape : List Nat) (data : List F) : Prop :=
  ValidShape shape ∧ data.length = shapeProd shape

theorem tensor_init_rejects_invalid_shape (shape : List Nat) (h_invalid : ¬ ValidShape shape) :
  (d : List F) → ¬ init_tensor_spec F shape d :=
  fun _ h_spec => h_invalid h_spec.left

theorem valid_shape_empty_is_false : ¬ ValidShape [] :=
  fun h => h

theorem valid_shape_zero_is_false : (xs : List Nat) → ¬ ValidShape (0 :: xs)
| [] => fun h => Nat.lt_irrefl 0 h
| _ :: _ => fun h => Nat.lt_irrefl 0 h.left

def usize_max : Nat := 18446744073709551615

def ValidDim (dim : Nat) : Prop :=
  dim > 0 ∧ dim ≤ usize_max / 2

def ValidLen (dim : Nat) (n : Nat) : Prop :=
  n = dim + dim

def transform_precondition (dim : Nat) (L : List F) : Prop :=
  ValidDim dim ∧ L.length = dim + dim

theorem oftb_transform_mismatched_size (dim : Nat) (L : List F) (h_mismatch : L.length ≠ dim + dim) :
  ¬ transform_precondition dim L :=
  fun h => h_mismatch h.right

def mixForwardCore (sa : ScaleAlgebra F) (dim : Nat) (L : List F) (_ : transform_precondition dim L) : List F :=
  forwardCore sa dim L

def mixBackwardCore (sa : ScaleAlgebra F) (dim : Nat) (L : List F) (_ : transform_precondition dim L) : List F :=
  backwardCore sa dim L

theorem length_forwardCore (sa : ScaleAlgebra F) (dim : Nat) (L : List F) (h : L.length = dim + dim) :
  (forwardCore sa dim L).length = dim + dim :=
  let x1 := (split_at dim L).1
  let x2 := (split_at dim L).2
  let h_splits : x1.length = dim ∧ x2.length = dim := split_at_lengths_gen dim dim L h
  let x1_new := List.zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) x1 x2
  let x2_new := List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) x1 x2
  let h_x1_new_len : x1_new.length = dim :=
    Eq.trans (length_zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) x1 x2 (Eq.trans h_splits.left (Eq.symm h_splits.right))) h_splits.left
  let h_x2_new_len : x2_new.length = dim :=
    Eq.trans (length_zipWith (fun a b => sa.mul (sa.add a b) sa.scale) x1 x2 (Eq.trans h_splits.left (Eq.symm h_splits.right))) h_splits.left
  let h_append := length_append x1_new x2_new
  let step1 : (x1_new ++ x2_new).length = x1_new.length + x2_new.length := h_append
  let step2 : x1_new.length + x2_new.length = dim + dim :=
    congr_add h_x1_new_len h_x2_new_len
  Eq.trans step1 step2

theorem length_backwardCore (sa : ScaleAlgebra F) (dim : Nat) (L : List F) (h : L.length = dim + dim) :
  (backwardCore sa dim L).length = dim + dim :=
  let g1 := (split_at dim L).1
  let g2 := (split_at dim L).2
  let h_splits : g1.length = dim ∧ g2.length = dim := split_at_lengths_gen dim dim L h
  let g1_new := List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) g1 g2
  let g2_new := List.zipWith (fun a b => sa.mul (sa.sub b a) sa.scale) g1 g2
  let h_g1_new_len : g1_new.length = dim :=
    Eq.trans (length_zipWith (fun a b => sa.mul (sa.add a b) sa.scale) g1 g2 (Eq.trans h_splits.left (Eq.symm h_splits.right))) h_splits.left
  let h_g2_new_len : g2_new.length = dim :=
    Eq.trans (length_zipWith (fun a b => sa.mul (sa.sub b a) sa.scale) g1 g2 (Eq.trans h_splits.left (Eq.symm h_splits.right))) h_splits.left
  let h_append := length_append g1_new g2_new
  let step1 : (g1_new ++ g2_new).length = g1_new.length + g2_new.length := h_append
  let step2 : g1_new.length + g2_new.length = dim + dim :=
    congr_add h_g1_new_len h_g2_new_len
  Eq.trans step1 step2

theorem mix_round_trip (sa : ScaleAlgebra F) (dim : Nat) (L : List F) (h : transform_precondition dim L) :
  let h_forward_pre : transform_precondition dim (mixForwardCore sa dim L h) :=
    ⟨h.left, length_forwardCore sa dim L h.right⟩
  mixBackwardCore sa dim (mixForwardCore sa dim L h) h_forward_pre = L :=
  oftb_invertible sa dim L h.right

theorem mix_round_trip_rev (sa : ScaleAlgebra F) (dim : Nat) (L : List F) (h : transform_precondition dim L) :
  let h_backward_pre : transform_precondition dim (mixBackwardCore sa dim L h) :=
    ⟨h.left, length_backwardCore sa dim L h.right⟩
  mixForwardCore sa dim (mixBackwardCore sa dim L h) h_backward_pre = L :=
  oftb_invertible_rev sa dim L h.right

namespace ZigOFTBSemantics

inductive ZigError where
| InvalidDimension : ZigError
| DimensionOverflow : ZigError
| DimensionMismatch : ZigError

inductive ZigResult (α : Type) where
| ok : α → ZigResult α
| err : ZigError → ZigResult α

inductive ZigOption (α : Type) where
| none : ZigOption α
| some : α → ZigOption α

structure OFTBState where
  dim : Nat

structure TensorMem (F : Type) where
  shape : List Nat
  data : List F

inductive Undefined (α : Type) where
| undefined : Undefined α

def VLEN : Nat := 8

def fractalScaleName : Nat := 7071067811865476

def usizeHalf : Nat := usize_max / 2

def checkedTotal (dim : Nat) : ZigOption Nat :=
  match Nat.decLe dim usizeHalf with
  | Decidable.isTrue _ => ZigOption.some (dim + dim)
  | Decidable.isFalse _ => ZigOption.none

def checkDim (dim : Nat) : ZigResult Unit :=
  match dim with
  | 0 => ZigResult.err ZigError.InvalidDimension
  | Nat.succ _ =>
    match Nat.decLt usizeHalf dim with
    | Decidable.isTrue _ => ZigResult.err ZigError.DimensionOverflow
    | Decidable.isFalse _ => ZigResult.ok Unit.unit

def checkLen (dim n : Nat) : ZigResult Unit :=
  match Nat.decEq n (dim + dim) with
  | Decidable.isTrue _ => ZigResult.ok Unit.unit
  | Decidable.isFalse _ => ZigResult.err ZigError.DimensionMismatch

def tensorSetData (t : TensorMem F) (d : List F) : TensorMem F :=
  { shape := t.shape, data := d }

def oftbInitSpec (d : Nat) (_ : ValidDim d) : OFTBState :=
  { dim := d }

def oftbDeinitSpec (_ : OFTBState) : Undefined OFTBState :=
  Undefined.undefined

def forwardPair (sa : ScaleAlgebra F) (a b : F) : F × F :=
  (sa.mul (sa.sub a b) sa.scale, sa.mul (sa.add a b) sa.scale)

def backwardPair (sa : ScaleAlgebra F) (a b : F) : F × F :=
  (sa.mul (sa.add a b) sa.scale, sa.mul (sa.sub b a) sa.scale)

def forwardPairList (sa : ScaleAlgebra F) : List F → List F → List F × List F
| [], [] => ([], [])
| a :: as, b :: bs =>
  let r := forwardPairList sa as bs
  (sa.mul (sa.sub a b) sa.scale :: r.1,
   sa.mul (sa.add a b) sa.scale :: r.2)
| [], _ :: _ => ([], [])
| _ :: _, [] => ([], [])

def backwardPairList (sa : ScaleAlgebra F) : List F → List F → List F × List F
| [], [] => ([], [])
| a :: as, b :: bs =>
  let r := backwardPairList sa as bs
  (sa.mul (sa.add a b) sa.scale :: r.1,
   sa.mul (sa.sub b a) sa.scale :: r.2)
| [], _ :: _ => ([], [])
| _ :: _, [] => ([], [])

def forwardLoopCore (sa : ScaleAlgebra F) (dim : Nat) (L : List F) : List F :=
  let x1 := (split_at dim L).1
  let x2 := (split_at dim L).2
  let r := forwardPairList sa x1 x2
  r.1 ++ r.2

def backwardLoopCore (sa : ScaleAlgebra F) (dim : Nat) (L : List F) : List F :=
  let g1 := (split_at dim L).1
  let g2 := (split_at dim L).2
  let r := backwardPairList sa g1 g2
  r.1 ++ r.2

def forwardChecked (sa : ScaleAlgebra F) (dim : Nat) (L : List F) : ZigResult (List F) :=
  match checkDim dim with
  | ZigResult.err e => ZigResult.err e
  | ZigResult.ok _ =>
    match checkLen dim L.length with
    | ZigResult.err e => ZigResult.err e
    | ZigResult.ok _ => ZigResult.ok (forwardCore sa dim L)

def backwardChecked (sa : ScaleAlgebra F) (dim : Nat) (L : List F) : ZigResult (List F) :=
  match checkDim dim with
  | ZigResult.err e => ZigResult.err e
  | ZigResult.ok _ =>
    match checkLen dim L.length with
    | ZigResult.err e => ZigResult.err e
    | ZigResult.ok _ => ZigResult.ok (backwardCore sa dim L)

def forwardInPlaceChecked (sa : ScaleAlgebra F) (o : OFTBState) (x : TensorMem F) : ZigResult (TensorMem F) :=
  match forwardChecked sa o.dim x.data with
  | ZigResult.err e => ZigResult.err e
  | ZigResult.ok d => ZigResult.ok (tensorSetData x d)

def backwardInPlaceChecked (sa : ScaleAlgebra F) (o : OFTBState) (grad : List F) : ZigResult (List F) :=
  backwardChecked sa o.dim grad

def mixForwardChecked (sa : ScaleAlgebra F) (o : OFTBState) (x : TensorMem F) : ZigResult (TensorMem F) :=
  forwardInPlaceChecked sa o x

def mixBackwardChecked (sa : ScaleAlgebra F) (o : OFTBState) (grad : List F) : ZigResult (List F) :=
  backwardInPlaceChecked sa o grad

def listGetNat : Nat → List F → ZigOption F
| _, [] => ZigOption.none
| 0, x :: _ => ZigOption.some x
| Nat.succ n, _ :: xs => listGetNat n xs

def listSetNat : Nat → F → List F → ZigOption (List F)
| _, _, [] => ZigOption.none
| 0, v, _ :: xs => ZigOption.some (v :: xs)
| Nat.succ n, v, x :: xs =>
  match listSetNat n v xs with
  | ZigOption.none => ZigOption.none
  | ZigOption.some ys => ZigOption.some (x :: ys)

def firstHalf (dim : Nat) (L : List F) : List F :=
  (split_at dim L).1

def secondHalf (dim : Nat) (L : List F) : List F :=
  (split_at dim L).2

def scalarForwardExpr (sa : ScaleAlgebra F) (a b : F) : F :=
  sa.mul (sa.sub a b) sa.scale

def scalarForwardExpr2 (sa : ScaleAlgebra F) (a b : F) : F :=
  sa.mul (sa.add a b) sa.scale

def scalarBackwardExpr1 (sa : ScaleAlgebra F) (a b : F) : F :=
  sa.mul (sa.add a b) sa.scale

def scalarBackwardExpr2 (sa : ScaleAlgebra F) (a b : F) : F :=
  sa.mul (sa.sub b a) sa.scale

theorem oftb_init_dim (d : Nat) (h : ValidDim d) :
  (oftbInitSpec d h).dim = d :=
  Eq.refl d

theorem oftb_deinit_result (o : OFTBState) :
  oftbDeinitSpec o = Undefined.undefined :=
  Eq.refl _

theorem tensor_set_data_shape (t : TensorMem F) (d : List F) :
  (tensorSetData t d).shape = t.shape :=
  Eq.refl t.shape

theorem tensor_set_data_data (t : TensorMem F) (d : List F) :
  (tensorSetData t d).data = d :=
  Eq.refl d

theorem checkDim_zero :
  checkDim 0 = ZigResult.err ZigError.InvalidDimension :=
  Eq.refl _

theorem checkDim_overflow (dim : Nat) (h0 : Not (dim = 0)) (hov : usizeHalf < dim) :
  checkDim dim = ZigResult.err ZigError.DimensionOverflow :=
  match dim with
  | 0 => False.elim (h0 (Eq.refl 0))
  | Nat.succ k =>
    match Nat.decLt usizeHalf (Nat.succ k) with
    | Decidable.isTrue _ => Eq.refl _
    | Decidable.isFalse hn => False.elim (hn hov)

theorem checkDim_ok (dim : Nat) (h0 : Not (dim = 0)) (hno : Not (usizeHalf < dim)) :
  checkDim dim = ZigResult.ok Unit.unit :=
  match dim with
  | 0 => False.elim (h0 (Eq.refl 0))
  | Nat.succ k =>
    match Nat.decLt usizeHalf (Nat.succ k) with
    | Decidable.isTrue hp => False.elim (hno hp)
    | Decidable.isFalse _ => Eq.refl _

theorem checkedTotal_none_on_overflow (dim : Nat) (h : Not (dim ≤ usizeHalf)) :
  checkedTotal dim = ZigOption.none :=
  match Nat.decLe dim usizeHalf with
  | Decidable.isTrue hp => False.elim (h hp)
  | Decidable.isFalse _ => Eq.refl _

theorem checkedTotal_some_on_no_overflow (dim : Nat) (h : dim ≤ usizeHalf) :
  checkedTotal dim = ZigOption.some (dim + dim) :=
  match Nat.decLe dim usizeHalf with
  | Decidable.isTrue _ => Eq.refl _
  | Decidable.isFalse hn => False.elim (hn h)

theorem checkLen_ok (dim n : Nat) (h : n = dim + dim) :
  checkLen dim n = ZigResult.ok Unit.unit :=
  match Nat.decEq n (dim + dim) with
  | Decidable.isTrue _ => Eq.refl _
  | Decidable.isFalse hn => False.elim (hn h)

theorem checkLen_mismatch (dim n : Nat) (h : Not (n = dim + dim)) :
  checkLen dim n = ZigResult.err ZigError.DimensionMismatch :=
  match Nat.decEq n (dim + dim) with
  | Decidable.isTrue hp => False.elim (h hp)
  | Decidable.isFalse _ => Eq.refl _

theorem forward_pair_first (sa : ScaleAlgebra F) (a b : F) :
  (forwardPair sa a b).1 = scalarForwardExpr sa a b :=
  Eq.refl _

theorem forward_pair_second (sa : ScaleAlgebra F) (a b : F) :
  (forwardPair sa a b).2 = scalarForwardExpr2 sa a b :=
  Eq.refl _

theorem backward_pair_first (sa : ScaleAlgebra F) (a b : F) :
  (backwardPair sa a b).1 = scalarBackwardExpr1 sa a b :=
  Eq.refl _

theorem backward_pair_second (sa : ScaleAlgebra F) (a b : F) :
  (backwardPair sa a b).2 = scalarBackwardExpr2 sa a b :=
  Eq.refl _

theorem forward_pair_inverse_first (sa : ScaleAlgebra F) (a b : F) :
  let p := forwardPair sa a b
  scalarBackwardExpr1 sa p.1 p.2 = a :=
  first_component_proof sa a b

theorem forward_pair_inverse_second (sa : ScaleAlgebra F) (a b : F) :
  let p := forwardPair sa a b
  scalarBackwardExpr2 sa p.1 p.2 = b :=
  second_component_proof sa a b

theorem backward_pair_inverse_first (sa : ScaleAlgebra F) (a b : F) :
  let p := backwardPair sa a b
  scalarForwardExpr sa p.1 p.2 = a :=
  first_component_proof_rev sa a b

theorem backward_pair_inverse_second (sa : ScaleAlgebra F) (a b : F) :
  let p := backwardPair sa a b
  scalarForwardExpr2 sa p.1 p.2 = b :=
  second_component_proof_rev sa a b

theorem forwardPairList_eq_zip (sa : ScaleAlgebra F) :
  (L1 L2 : List F) → L1.length = L2.length →
  forwardPairList sa L1 L2 =
    (List.zipWith (fun a b => sa.mul (sa.sub a b) sa.scale) L1 L2,
     List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) L1 L2)
| [], [], _ => Eq.refl _
| a :: as, b :: bs, h =>
  let h_len : as.length = bs.length := succ_inj h
  let rec_res := forwardPairList_eq_zip sa as bs h_len
  congrArg (fun p =>
    (sa.mul (sa.sub a b) sa.scale :: p.1,
     sa.mul (sa.add a b) sa.scale :: p.2)) rec_res
| _ :: _, [], h => False.elim (succ_not_zero _ h)
| [], _ :: _, h => False.elim (zero_not_succ _ h)

theorem backwardPairList_eq_zip (sa : ScaleAlgebra F) :
  (L1 L2 : List F) → L1.length = L2.length →
  backwardPairList sa L1 L2 =
    (List.zipWith (fun a b => sa.mul (sa.add a b) sa.scale) L1 L2,
     List.zipWith (fun a b => sa.mul (sa.sub b a) sa.scale) L1 L2)
| [], [], _ => Eq.refl _
| a :: as, b :: bs, h =>
  let h_len : as.length = bs.length := succ_inj h
  let rec_res := backwardPairList_eq_zip sa as bs h_len
  congrArg (fun p =>
    (sa.mul (sa.add a b) sa.scale :: p.1,
     sa.mul (sa.sub b a) sa.scale :: p.2)) rec_res
| _ :: _, [], h => False.elim (succ_not_zero _ h)
| [], _ :: _, h => False.elim (zero_not_succ _ h)

theorem forwardLoopCore_eq_forwardCore (sa : ScaleAlgebra F) (dim : Nat) (L : List F) (h : L.length = dim + dim) :
  forwardLoopCore sa dim L = forwardCore sa dim L :=
  let x1 := (split_at dim L).1
  let x2 := (split_at dim L).2
  let h_splits : x1.length = dim ∧ x2.length = dim := split_at_lengths_gen dim dim L h
  let h_len : x1.length = x2.length := Eq.trans h_splits.left (Eq.symm h_splits.right)
  let h_pair := forwardPairList_eq_zip sa x1 x2 h_len
  congrArg (fun p => p.1 ++ p.2) h_pair

theorem backwardLoopCore_eq_backwardCore (sa : ScaleAlgebra F) (dim : Nat) (L : List F) (h : L.length = dim + dim) :
  backwardLoopCore sa dim L = backwardCore sa dim L :=
  let g1 := (split_at dim L).1
  let g2 := (split_at dim L).2
  let h_splits : g1.length = dim ∧ g2.length = dim := split_at_lengths_gen dim dim L h
  let h_len : g1.length = g2.length := Eq.trans h_splits.left (Eq.symm h_splits.right)
  let h_pair := backwardPairList_eq_zip sa g1 g2 h_len
  congrArg (fun p => p.1 ++ p.2) h_pair

theorem forward_checked_invalid_dimension (sa : ScaleAlgebra F) (L : List F) :
  forwardChecked sa 0 L = ZigResult.err ZigError.InvalidDimension :=
  Eq.refl _

theorem backward_checked_invalid_dimension (sa : ScaleAlgebra F) (L : List F) :
  backwardChecked sa 0 L = ZigResult.err ZigError.InvalidDimension :=
  Eq.refl _

theorem forward_checked_overflow (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h0 : Not (dim = 0)) (hov : usizeHalf < dim) :
  forwardChecked sa dim L = ZigResult.err ZigError.DimensionOverflow :=
  let hdim := checkDim_overflow dim h0 hov
  match hdim with
  | Eq.refl _ => Eq.refl _

theorem backward_checked_overflow (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h0 : Not (dim = 0)) (hov : usizeHalf < dim) :
  backwardChecked sa dim L = ZigResult.err ZigError.DimensionOverflow :=
  let hdim := checkDim_overflow dim h0 hov
  match hdim with
  | Eq.refl _ => Eq.refl _

theorem forward_checked_mismatch (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h0 : Not (dim = 0)) (hno : Not (usizeHalf < dim)) (hm : Not (L.length = dim + dim)) :
  forwardChecked sa dim L = ZigResult.err ZigError.DimensionMismatch :=
  let hdim := checkDim_ok dim h0 hno
  let hlen := checkLen_mismatch dim L.length hm
  match hdim, hlen with
  | Eq.refl _, Eq.refl _ => Eq.refl _

theorem backward_checked_mismatch (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h0 : Not (dim = 0)) (hno : Not (usizeHalf < dim)) (hm : Not (L.length = dim + dim)) :
  backwardChecked sa dim L = ZigResult.err ZigError.DimensionMismatch :=
  let hdim := checkDim_ok dim h0 hno
  let hlen := checkLen_mismatch dim L.length hm
  match hdim, hlen with
  | Eq.refl _, Eq.refl _ => Eq.refl _

theorem forward_checked_success (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h0 : Not (dim = 0)) (hno : Not (usizeHalf < dim)) (hlen : L.length = dim + dim) :
  forwardChecked sa dim L = ZigResult.ok (forwardCore sa dim L) :=
  let hdim := checkDim_ok dim h0 hno
  let hlen2 := checkLen_ok dim L.length hlen
  match hdim, hlen2 with
  | Eq.refl _, Eq.refl _ => Eq.refl _

theorem backward_checked_success (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h0 : Not (dim = 0)) (hno : Not (usizeHalf < dim)) (hlen : L.length = dim + dim) :
  backwardChecked sa dim L = ZigResult.ok (backwardCore sa dim L) :=
  let hdim := checkDim_ok dim h0 hno
  let hlen2 := checkLen_ok dim L.length hlen
  match hdim, hlen2 with
  | Eq.refl _, Eq.refl _ => Eq.refl _

theorem forward_in_place_success (sa : ScaleAlgebra F) (o : OFTBState) (x : TensorMem F)
  (h0 : Not (o.dim = 0)) (hno : Not (usizeHalf < o.dim)) (hlen : x.data.length = o.dim + o.dim) :
  forwardInPlaceChecked sa o x = ZigResult.ok (tensorSetData x (forwardCore sa o.dim x.data)) :=
  let hf := forward_checked_success sa o.dim x.data h0 hno hlen
  match hf with
  | Eq.refl _ => Eq.refl _

theorem backward_in_place_success (sa : ScaleAlgebra F) (o : OFTBState) (grad : List F)
  (h0 : Not (o.dim = 0)) (hno : Not (usizeHalf < o.dim)) (hlen : grad.length = o.dim + o.dim) :
  backwardInPlaceChecked sa o grad = ZigResult.ok (backwardCore sa o.dim grad) :=
  backward_checked_success sa o.dim grad h0 hno hlen

theorem mix_forward_is_forward (sa : ScaleAlgebra F) (o : OFTBState) (x : TensorMem F) :
  mixForwardChecked sa o x = forwardInPlaceChecked sa o x :=
  Eq.refl _

theorem mix_backward_is_backward (sa : ScaleAlgebra F) (o : OFTBState) (grad : List F) :
  mixBackwardChecked sa o grad = backwardInPlaceChecked sa o grad :=
  Eq.refl _

theorem forward_in_place_preserves_shape (sa : ScaleAlgebra F) (o : OFTBState) (x y : TensorMem F)
  (h : forwardInPlaceChecked sa o x = ZigResult.ok y) :
  y.shape = x.shape :=
  match forwardChecked sa o.dim x.data with
  | ZigResult.err e =>
    False.elim (nomatch h)
  | ZigResult.ok d =>
    match h with
    | Eq.refl _ => Eq.refl x.shape

theorem forward_in_place_sets_data (sa : ScaleAlgebra F) (o : OFTBState) (x y : TensorMem F)
  (h : forwardInPlaceChecked sa o x = ZigResult.ok y) :
  y.data =
    match forwardChecked sa o.dim x.data with
    | ZigResult.err _ => x.data
    | ZigResult.ok d => d :=
  match forwardChecked sa o.dim x.data with
  | ZigResult.err e =>
    False.elim (nomatch h)
  | ZigResult.ok d =>
    match h with
    | Eq.refl _ => Eq.refl d

theorem forward_checked_length (sa : ScaleAlgebra F) (dim : Nat) (L out : List F)
  (hmain : forwardChecked sa dim L = ZigResult.ok out)
  (h0 : Not (dim = 0)) (hno : Not (usizeHalf < dim)) (hlen : L.length = dim + dim) :
  out.length = dim + dim :=
  let hs := forward_checked_success sa dim L h0 hno hlen
  match Eq.trans (Eq.symm hs) hmain with
  | Eq.refl _ => length_forwardCore sa dim L hlen

theorem backward_checked_length (sa : ScaleAlgebra F) (dim : Nat) (L out : List F)
  (hmain : backwardChecked sa dim L = ZigResult.ok out)
  (h0 : Not (dim = 0)) (hno : Not (usizeHalf < dim)) (hlen : L.length = dim + dim) :
  out.length = dim + dim :=
  let hs := backward_checked_success sa dim L h0 hno hlen
  match Eq.trans (Eq.symm hs) hmain with
  | Eq.refl _ => length_backwardCore sa dim L hlen

theorem forward_backward_checked_roundtrip (sa : ScaleAlgebra F) (dim : Nat) (L M : List F)
  (h0 : Not (dim = 0)) (hno : Not (usizeHalf < dim)) (hlen : L.length = dim + dim)
  (hf : forwardChecked sa dim L = ZigResult.ok M) :
  backwardChecked sa dim M = ZigResult.ok L :=
  let hs := forward_checked_success sa dim L h0 hno hlen
  match Eq.trans (Eq.symm hs) hf with
  | Eq.refl _ =>
    let hmlen := length_forwardCore sa dim L hlen
    let hb := backward_checked_success sa dim (forwardCore sa dim L) h0 hno hmlen
    let hinv := oftb_invertible sa dim L hlen
    match hb, hinv with
    | Eq.refl _, Eq.refl _ => Eq.refl _

theorem backward_forward_checked_roundtrip (sa : ScaleAlgebra F) (dim : Nat) (L M : List F)
  (h0 : Not (dim = 0)) (hno : Not (usizeHalf < dim)) (hlen : L.length = dim + dim)
  (hb0 : backwardChecked sa dim L = ZigResult.ok M) :
  forwardChecked sa dim M = ZigResult.ok L :=
  let hs := backward_checked_success sa dim L h0 hno hlen
  match Eq.trans (Eq.symm hs) hb0 with
  | Eq.refl _ =>
    let hmlen := length_backwardCore sa dim L hlen
    let hf := forward_checked_success sa dim (backwardCore sa dim L) h0 hno hmlen
    let hinv := oftb_invertible_rev sa dim L hlen
    match hf, hinv with
    | Eq.refl _, Eq.refl _ => Eq.refl _

theorem listGetNat_zero_cons (x : F) (xs : List F) :
  listGetNat 0 (x :: xs) = ZigOption.some x :=
  Eq.refl _

theorem listGetNat_succ_cons (n : Nat) (x : F) (xs : List F) :
  listGetNat (Nat.succ n) (x :: xs) = listGetNat n xs :=
  Eq.refl _

theorem listGetNat_nil (n : Nat) :
  listGetNat (F := F) n [] = ZigOption.none :=
  match n with
  | 0 => Eq.refl _
  | Nat.succ _ => Eq.refl _

theorem listSetNat_zero_cons (v x : F) (xs : List F) :
  listSetNat 0 v (x :: xs) = ZigOption.some (v :: xs) :=
  Eq.refl _

theorem listSetNat_nil (n : Nat) (v : F) :
  listSetNat n v [] = ZigOption.none :=
  match n with
  | 0 => Eq.refl _
  | Nat.succ _ => Eq.refl _

theorem listSetNat_succ_cons_none (n : Nat) (v x : F) (xs : List F)
  (h : listSetNat n v xs = ZigOption.none) :
  listSetNat (Nat.succ n) v (x :: xs) = ZigOption.none :=
  match h with
  | Eq.refl _ => Eq.refl _

theorem listSetNat_succ_cons_some (n : Nat) (v x : F) (xs ys : List F)
  (h : listSetNat n v xs = ZigOption.some ys) :
  listSetNat (Nat.succ n) v (x :: xs) = ZigOption.some (x :: ys) :=
  match h with
  | Eq.refl _ => Eq.refl _

theorem split_memory_halves_lengths (dim : Nat) (L : List F) (h : L.length = dim + dim) :
  (firstHalf dim L).length = dim ∧ (secondHalf dim L).length = dim :=
  split_at_lengths_gen dim dim L h

theorem split_memory_reconstruct (dim : Nat) (L : List F) :
  firstHalf dim L ++ secondHalf dim L = L :=
  split_at_reconstruct dim L

theorem forward_scalar_loop_matches_public_core (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h : L.length = dim + dim) :
  forwardLoopCore sa dim L = forwardCore sa dim L :=
  forwardLoopCore_eq_forwardCore sa dim L h

theorem backward_scalar_loop_matches_public_core (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h : L.length = dim + dim) :
  backwardLoopCore sa dim L = backwardCore sa dim L :=
  backwardLoopCore_eq_backwardCore sa dim L h

theorem forward_core_has_two_halves (sa : ScaleAlgebra F) (dim : Nat) (L : List F) (h : L.length = dim + dim) :
  (split_at dim (forwardCore sa dim L)).1.length = dim ∧
  (split_at dim (forwardCore sa dim L)).2.length = dim :=
  let hlen := length_forwardCore sa dim L h
  split_at_lengths_gen dim dim (forwardCore sa dim L) hlen

theorem backward_core_has_two_halves (sa : ScaleAlgebra F) (dim : Nat) (L : List F) (h : L.length = dim + dim) :
  (split_at dim (backwardCore sa dim L)).1.length = dim ∧
  (split_at dim (backwardCore sa dim L)).2.length = dim :=
  let hlen := length_backwardCore sa dim L h
  split_at_lengths_gen dim dim (backwardCore sa dim L) hlen

theorem forward_no_write_outside_data_shape (sa : ScaleAlgebra F) (o : OFTBState) (x y : TensorMem F)
  (h : forwardInPlaceChecked sa o x = ZigResult.ok y) :
  y.shape = x.shape :=
  forward_in_place_preserves_shape sa o x y h

theorem mix_forward_shape (sa : ScaleAlgebra F) (o : OFTBState) (x y : TensorMem F)
  (h : mixForwardChecked sa o x = ZigResult.ok y) :
  y.shape = x.shape :=
  forward_in_place_preserves_shape sa o x y h

theorem mix_backward_data_result (sa : ScaleAlgebra F) (o : OFTBState) (grad out : List F)
  (h : mixBackwardChecked sa o grad = ZigResult.ok out) :
  backwardInPlaceChecked sa o grad = ZigResult.ok out :=
  h

theorem valid_dim_not_zero (dim : Nat) (h : ValidDim dim) :
  Not (dim = 0) :=
  fun hz =>
    match hz with
    | Eq.refl _ => Nat.lt_irrefl 0 h.left

theorem valid_dim_no_overflow_lt (dim : Nat) (h : ValidDim dim) :
  Not (usizeHalf < dim) :=
  fun hov =>
    Nat.lt_irrefl usizeHalf (Nat.lt_of_lt_of_le hov h.right)

theorem init_forward_public_post (sa : ScaleAlgebra F) (dim : Nat) (hd : ValidDim dim) (x : TensorMem F)
  (hlen : x.data.length = dim + dim) :
  forwardInPlaceChecked sa (oftbInitSpec dim hd) x = ZigResult.ok (tensorSetData x (forwardCore sa dim x.data)) :=
  let h0 := valid_dim_not_zero dim hd
  let hno := valid_dim_no_overflow_lt dim hd
  forward_in_place_success sa (oftbInitSpec dim hd) x h0 hno hlen

theorem init_backward_public_post (sa : ScaleAlgebra F) (dim : Nat) (hd : ValidDim dim) (grad : List F)
  (hlen : grad.length = dim + dim) :
  backwardInPlaceChecked sa (oftbInitSpec dim hd) grad = ZigResult.ok (backwardCore sa dim grad) :=
  let h0 := valid_dim_not_zero dim hd
  let hno := valid_dim_no_overflow_lt dim hd
  backward_in_place_success sa (oftbInitSpec dim hd) grad h0 hno hlen

theorem public_mix_forward_post (sa : ScaleAlgebra F) (dim : Nat) (hd : ValidDim dim) (x : TensorMem F)
  (hlen : x.data.length = dim + dim) :
  mixForwardChecked sa (oftbInitSpec dim hd) x = ZigResult.ok (tensorSetData x (forwardCore sa dim x.data)) :=
  init_forward_public_post sa dim hd x hlen

theorem public_mix_backward_post (sa : ScaleAlgebra F) (dim : Nat) (hd : ValidDim dim) (grad : List F)
  (hlen : grad.length = dim + dim) :
  mixBackwardChecked sa (oftbInitSpec dim hd) grad = ZigResult.ok (backwardCore sa dim grad) :=
  init_backward_public_post sa dim hd grad hlen

theorem public_round_trip_after_init (sa : ScaleAlgebra F) (dim : Nat) (hd : ValidDim dim) (L M : List F)
  (hlen : L.length = dim + dim)
  (hf : forwardChecked sa (oftbInitSpec dim hd).dim L = ZigResult.ok M) :
  backwardChecked sa (oftbInitSpec dim hd).dim M = ZigResult.ok L :=
  let h0 := valid_dim_not_zero dim hd
  let hno := valid_dim_no_overflow_lt dim hd
  forward_backward_checked_roundtrip sa dim L M h0 hno hlen hf

theorem public_round_trip_rev_after_init (sa : ScaleAlgebra F) (dim : Nat) (hd : ValidDim dim) (L M : List F)
  (hlen : L.length = dim + dim)
  (hb : backwardChecked sa (oftbInitSpec dim hd).dim L = ZigResult.ok M) :
  forwardChecked sa (oftbInitSpec dim hd).dim M = ZigResult.ok L :=
  let h0 := valid_dim_not_zero dim hd
  let hno := valid_dim_no_overflow_lt dim hd
  backward_forward_checked_roundtrip sa dim L M h0 hno hlen hb


theorem vlen_value_exact :
  VLEN = 8 :=
  Eq.refl 8

theorem usize_half_unfolds :
  usizeHalf = usize_max / 2 :=
  Eq.refl _

theorem fractal_scale_decimal_record :
  fractalScaleName = 7071067811865476 :=
  Eq.refl _

theorem forward_expr_exact_statement (sa : ScaleAlgebra F) (a b : F) :
  scalarForwardExpr sa a b = sa.mul (sa.sub a b) sa.scale :=
  let step0 : scalarForwardExpr sa a b = sa.mul (sa.sub a b) sa.scale := Eq.refl _
  let step1 : sa.mul (sa.sub a b) sa.scale = sa.mul (sa.sub a b) sa.scale := Eq.refl _
  let step2 : scalarForwardExpr sa a b = sa.mul (sa.sub a b) sa.scale := Eq.trans step0 step1
  step2

theorem forward_expr2_exact_statement (sa : ScaleAlgebra F) (a b : F) :
  scalarForwardExpr2 sa a b = sa.mul (sa.add a b) sa.scale :=
  let step0 : scalarForwardExpr2 sa a b = sa.mul (sa.add a b) sa.scale := Eq.refl _
  let step1 : sa.mul (sa.add a b) sa.scale = sa.mul (sa.add a b) sa.scale := Eq.refl _
  let step2 : scalarForwardExpr2 sa a b = sa.mul (sa.add a b) sa.scale := Eq.trans step0 step1
  step2

theorem backward_expr1_exact_statement (sa : ScaleAlgebra F) (a b : F) :
  scalarBackwardExpr1 sa a b = sa.mul (sa.add a b) sa.scale :=
  let step0 : scalarBackwardExpr1 sa a b = sa.mul (sa.add a b) sa.scale := Eq.refl _
  let step1 : sa.mul (sa.add a b) sa.scale = sa.mul (sa.add a b) sa.scale := Eq.refl _
  let step2 : scalarBackwardExpr1 sa a b = sa.mul (sa.add a b) sa.scale := Eq.trans step0 step1
  step2

theorem backward_expr2_exact_statement (sa : ScaleAlgebra F) (a b : F) :
  scalarBackwardExpr2 sa a b = sa.mul (sa.sub b a) sa.scale :=
  let step0 : scalarBackwardExpr2 sa a b = sa.mul (sa.sub b a) sa.scale := Eq.refl _
  let step1 : sa.mul (sa.sub b a) sa.scale = sa.mul (sa.sub b a) sa.scale := Eq.refl _
  let step2 : scalarBackwardExpr2 sa a b = sa.mul (sa.sub b a) sa.scale := Eq.trans step0 step1
  step2

theorem forward_pair_unfold_exact (sa : ScaleAlgebra F) (a b : F) :
  forwardPair sa a b = (scalarForwardExpr sa a b, scalarForwardExpr2 sa a b) :=
  let step0 : forwardPair sa a b = (sa.mul (sa.sub a b) sa.scale, sa.mul (sa.add a b) sa.scale) := Eq.refl _
  let step1 : (sa.mul (sa.sub a b) sa.scale, sa.mul (sa.add a b) sa.scale) =
    (scalarForwardExpr sa a b, scalarForwardExpr2 sa a b) := Eq.refl _
  Eq.trans step0 step1

theorem backward_pair_unfold_exact (sa : ScaleAlgebra F) (a b : F) :
  backwardPair sa a b = (scalarBackwardExpr1 sa a b, scalarBackwardExpr2 sa a b) :=
  let step0 : backwardPair sa a b = (sa.mul (sa.add a b) sa.scale, sa.mul (sa.sub b a) sa.scale) := Eq.refl _
  let step1 : (sa.mul (sa.add a b) sa.scale, sa.mul (sa.sub b a) sa.scale) =
    (scalarBackwardExpr1 sa a b, scalarBackwardExpr2 sa a b) := Eq.refl _
  Eq.trans step0 step1

theorem forwardPairList_nil_exact (sa : ScaleAlgebra F) :
  forwardPairList sa [] [] = ([], []) :=
  Eq.refl _

theorem backwardPairList_nil_exact (sa : ScaleAlgebra F) :
  backwardPairList sa [] [] = ([], []) :=
  Eq.refl _

theorem forwardPairList_cons_exact (sa : ScaleAlgebra F) (a b : F) (as bs : List F) :
  forwardPairList sa (a :: as) (b :: bs) =
    let r := forwardPairList sa as bs
    (scalarForwardExpr sa a b :: r.1, scalarForwardExpr2 sa a b :: r.2) :=
  Eq.refl _

theorem backwardPairList_cons_exact (sa : ScaleAlgebra F) (a b : F) (as bs : List F) :
  backwardPairList sa (a :: as) (b :: bs) =
    let r := backwardPairList sa as bs
    (scalarBackwardExpr1 sa a b :: r.1, scalarBackwardExpr2 sa a b :: r.2) :=
  Eq.refl _

theorem forwardPairList_left_empty_mismatch (sa : ScaleAlgebra F) (b : F) (bs : List F) :
  forwardPairList sa [] (b :: bs) = ([], []) :=
  Eq.refl _

theorem forwardPairList_right_empty_mismatch (sa : ScaleAlgebra F) (a : F) (as : List F) :
  forwardPairList sa (a :: as) [] = ([], []) :=
  Eq.refl _

theorem backwardPairList_left_empty_mismatch (sa : ScaleAlgebra F) (b : F) (bs : List F) :
  backwardPairList sa [] (b :: bs) = ([], []) :=
  Eq.refl _

theorem backwardPairList_right_empty_mismatch (sa : ScaleAlgebra F) (a : F) (as : List F) :
  backwardPairList sa (a :: as) [] = ([], []) :=
  Eq.refl _

theorem forwardLoopCore_unfold_exact (sa : ScaleAlgebra F) (dim : Nat) (L : List F) :
  forwardLoopCore sa dim L =
    let x1 := (split_at dim L).1
    let x2 := (split_at dim L).2
    let r := forwardPairList sa x1 x2
    r.1 ++ r.2 :=
  Eq.refl _

theorem backwardLoopCore_unfold_exact (sa : ScaleAlgebra F) (dim : Nat) (L : List F) :
  backwardLoopCore sa dim L =
    let g1 := (split_at dim L).1
    let g2 := (split_at dim L).2
    let r := backwardPairList sa g1 g2
    r.1 ++ r.2 :=
  Eq.refl _

theorem forwardChecked_unfold_exact (sa : ScaleAlgebra F) (dim : Nat) (L : List F) :
  forwardChecked sa dim L =
    match checkDim dim with
    | ZigResult.err e => ZigResult.err e
    | ZigResult.ok _ =>
      match checkLen dim L.length with
      | ZigResult.err e => ZigResult.err e
      | ZigResult.ok _ => ZigResult.ok (forwardCore sa dim L) :=
  Eq.refl _

theorem backwardChecked_unfold_exact (sa : ScaleAlgebra F) (dim : Nat) (L : List F) :
  backwardChecked sa dim L =
    match checkDim dim with
    | ZigResult.err e => ZigResult.err e
    | ZigResult.ok _ =>
      match checkLen dim L.length with
      | ZigResult.err e => ZigResult.err e
      | ZigResult.ok _ => ZigResult.ok (backwardCore sa dim L) :=
  Eq.refl _

theorem forwardInPlace_unfold_exact (sa : ScaleAlgebra F) (o : OFTBState) (x : TensorMem F) :
  forwardInPlaceChecked sa o x =
    match forwardChecked sa o.dim x.data with
    | ZigResult.err e => ZigResult.err e
    | ZigResult.ok d => ZigResult.ok (tensorSetData x d) :=
  Eq.refl _

theorem backwardInPlace_unfold_exact (sa : ScaleAlgebra F) (o : OFTBState) (grad : List F) :
  backwardInPlaceChecked sa o grad = backwardChecked sa o.dim grad :=
  Eq.refl _

theorem mixForward_unfold_exact (sa : ScaleAlgebra F) (o : OFTBState) (x : TensorMem F) :
  mixForwardChecked sa o x = forwardInPlaceChecked sa o x :=
  Eq.refl _

theorem mixBackward_unfold_exact (sa : ScaleAlgebra F) (o : OFTBState) (grad : List F) :
  mixBackwardChecked sa o grad = backwardInPlaceChecked sa o grad :=
  Eq.refl _

theorem listGetNat_zero_exact (x : F) (xs : List F) :
  listGetNat 0 (x :: xs) = ZigOption.some x :=
  Eq.refl _

theorem listGetNat_one_exact (x y : F) (xs : List F) :
  listGetNat 1 (x :: y :: xs) = ZigOption.some y :=
  Eq.refl _

theorem listSetNat_zero_exact (v x : F) (xs : List F) :
  listSetNat 0 v (x :: xs) = ZigOption.some (v :: xs) :=
  Eq.refl _

theorem listSetNat_one_exact (v x y : F) (xs : List F) :
  listSetNat 1 v (x :: y :: xs) = ZigOption.some (x :: v :: xs) :=
  Eq.refl _

theorem checkLen_uses_double_dim (dim : Nat) :
  checkLen dim (dim + dim) = ZigResult.ok Unit.unit :=
  checkLen_ok dim (dim + dim) (Eq.refl _)

theorem checkedTotal_uses_same_double (dim : Nat) (h : dim ≤ usizeHalf) :
  checkedTotal dim = ZigOption.some (dim + dim) :=
  checkedTotal_some_on_no_overflow dim h

theorem transform_precondition_contains_len (dim : Nat) (L : List F) (h : transform_precondition dim L) :
  L.length = dim + dim :=
  h.right

theorem transform_precondition_contains_valid_dim (dim : Nat) (L : List F) (h : transform_precondition dim L) :
  ValidDim dim :=
  h.left

theorem valid_dim_contains_positive (dim : Nat) (h : ValidDim dim) :
  dim > 0 :=
  h.left

theorem valid_dim_contains_bound (dim : Nat) (h : ValidDim dim) :
  dim ≤ usize_max / 2 :=
  h.right

theorem forward_length_from_precondition (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h : transform_precondition dim L) :
  (forwardCore sa dim L).length = dim + dim :=
  length_forwardCore sa dim L h.right

theorem backward_length_from_precondition (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h : transform_precondition dim L) :
  (backwardCore sa dim L).length = dim + dim :=
  length_backwardCore sa dim L h.right

end ZigOFTBSemantics

namespace ZigOFTBSemantics

def forwardVectorizedPairList (sa : ScaleAlgebra F) : List F → List F → List F × List F
| a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: as,
  b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs =>
  let r := forwardVectorizedPairList sa as bs
  (scalarForwardExpr sa a0 b0 :: scalarForwardExpr sa a1 b1 ::
   scalarForwardExpr sa a2 b2 :: scalarForwardExpr sa a3 b3 ::
   scalarForwardExpr sa a4 b4 :: scalarForwardExpr sa a5 b5 ::
   scalarForwardExpr sa a6 b6 :: scalarForwardExpr sa a7 b7 :: r.1,
   scalarForwardExpr2 sa a0 b0 :: scalarForwardExpr2 sa a1 b1 ::
   scalarForwardExpr2 sa a2 b2 :: scalarForwardExpr2 sa a3 b3 ::
   scalarForwardExpr2 sa a4 b4 :: scalarForwardExpr2 sa a5 b5 ::
   scalarForwardExpr2 sa a6 b6 :: scalarForwardExpr2 sa a7 b7 :: r.2)
| L1, L2 => forwardPairList sa L1 L2

def backwardVectorizedPairList (sa : ScaleAlgebra F) : List F → List F → List F × List F
| a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: as,
  b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs =>
  let r := backwardVectorizedPairList sa as bs
  (scalarBackwardExpr1 sa a0 b0 :: scalarBackwardExpr1 sa a1 b1 ::
   scalarBackwardExpr1 sa a2 b2 :: scalarBackwardExpr1 sa a3 b3 ::
   scalarBackwardExpr1 sa a4 b4 :: scalarBackwardExpr1 sa a5 b5 ::
   scalarBackwardExpr1 sa a6 b6 :: scalarBackwardExpr1 sa a7 b7 :: r.1,
   scalarBackwardExpr2 sa a0 b0 :: scalarBackwardExpr2 sa a1 b1 ::
   scalarBackwardExpr2 sa a2 b2 :: scalarBackwardExpr2 sa a3 b3 ::
   scalarBackwardExpr2 sa a4 b4 :: scalarBackwardExpr2 sa a5 b5 ::
   scalarBackwardExpr2 sa a6 b6 :: scalarBackwardExpr2 sa a7 b7 :: r.2)
| L1, L2 => backwardPairList sa L1 L2

def forwardVectorizedCore (sa : ScaleAlgebra F) (dim : Nat) (L : List F) : List F :=
  let x1 := firstHalf dim L
  let x2 := secondHalf dim L
  let r := forwardVectorizedPairList sa x1 x2
  r.1 ++ r.2

def backwardVectorizedCore (sa : ScaleAlgebra F) (dim : Nat) (L : List F) : List F :=
  let g1 := firstHalf dim L
  let g2 := secondHalf dim L
  let r := backwardVectorizedPairList sa g1 g2
  r.1 ++ r.2

theorem forwardVectorizedPairList_eq_scalar (sa : ScaleAlgebra F) :
  (L1 L2 : List F) → forwardVectorizedPairList sa L1 L2 = forwardPairList sa L1 L2
| a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: as,
  b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs =>
  let rec_res := forwardVectorizedPairList_eq_scalar sa as bs
  congrArg (fun p =>
    (scalarForwardExpr sa a0 b0 :: scalarForwardExpr sa a1 b1 ::
     scalarForwardExpr sa a2 b2 :: scalarForwardExpr sa a3 b3 ::
     scalarForwardExpr sa a4 b4 :: scalarForwardExpr sa a5 b5 ::
     scalarForwardExpr sa a6 b6 :: scalarForwardExpr sa a7 b7 :: p.1,
     scalarForwardExpr2 sa a0 b0 :: scalarForwardExpr2 sa a1 b1 ::
     scalarForwardExpr2 sa a2 b2 :: scalarForwardExpr2 sa a3 b3 ::
     scalarForwardExpr2 sa a4 b4 :: scalarForwardExpr2 sa a5 b5 ::
     scalarForwardExpr2 sa a6 b6 :: scalarForwardExpr2 sa a7 b7 :: p.2)) rec_res
| L1, L2 => Eq.refl (forwardPairList sa L1 L2)

theorem backwardVectorizedPairList_eq_scalar (sa : ScaleAlgebra F) :
  (L1 L2 : List F) → backwardVectorizedPairList sa L1 L2 = backwardPairList sa L1 L2
| a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: as,
  b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs =>
  let rec_res := backwardVectorizedPairList_eq_scalar sa as bs
  congrArg (fun p =>
    (scalarBackwardExpr1 sa a0 b0 :: scalarBackwardExpr1 sa a1 b1 ::
     scalarBackwardExpr1 sa a2 b2 :: scalarBackwardExpr1 sa a3 b3 ::
     scalarBackwardExpr1 sa a4 b4 :: scalarBackwardExpr1 sa a5 b5 ::
     scalarBackwardExpr1 sa a6 b6 :: scalarBackwardExpr1 sa a7 b7 :: p.1,
     scalarBackwardExpr2 sa a0 b0 :: scalarBackwardExpr2 sa a1 b1 ::
     scalarBackwardExpr2 sa a2 b2 :: scalarBackwardExpr2 sa a3 b3 ::
     scalarBackwardExpr2 sa a4 b4 :: scalarBackwardExpr2 sa a5 b5 ::
     scalarBackwardExpr2 sa a6 b6 :: scalarBackwardExpr2 sa a7 b7 :: p.2)) rec_res
| L1, L2 => Eq.refl (backwardPairList sa L1 L2)

theorem forwardVectorizedCore_eq_loop (sa : ScaleAlgebra F) (dim : Nat) (L : List F) :
  forwardVectorizedCore sa dim L = forwardLoopCore sa dim L :=
  let x1 := firstHalf dim L
  let x2 := secondHalf dim L
  let pair_eq := forwardVectorizedPairList_eq_scalar sa x1 x2
  congrArg (fun p => p.1 ++ p.2) pair_eq

theorem backwardVectorizedCore_eq_loop (sa : ScaleAlgebra F) (dim : Nat) (L : List F) :
  backwardVectorizedCore sa dim L = backwardLoopCore sa dim L :=
  let g1 := firstHalf dim L
  let g2 := secondHalf dim L
  let pair_eq := backwardVectorizedPairList_eq_scalar sa g1 g2
  congrArg (fun p => p.1 ++ p.2) pair_eq

theorem forwardVectorizedCore_eq_core (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h : L.length = dim + dim) :
  forwardVectorizedCore sa dim L = forwardCore sa dim L :=
  let step1 := forwardVectorizedCore_eq_loop sa dim L
  let step2 := forwardLoopCore_eq_forwardCore sa dim L h
  Eq.trans step1 step2

theorem backwardVectorizedCore_eq_core (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h : L.length = dim + dim) :
  backwardVectorizedCore sa dim L = backwardCore sa dim L :=
  let step1 := backwardVectorizedCore_eq_loop sa dim L
  let step2 := backwardLoopCore_eq_backwardCore sa dim L h
  Eq.trans step1 step2

theorem forwardVectorizedCore_round_trip (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h : L.length = dim + dim) :
  backwardVectorizedCore sa dim (forwardVectorizedCore sa dim L) = L :=
  let vf := forwardVectorizedCore_eq_core sa dim L h
  let hlen : (forwardCore sa dim L).length = dim + dim := length_forwardCore sa dim L h
  let vb := backwardVectorizedCore_eq_core sa dim (forwardCore sa dim L) hlen
  let inv := oftb_invertible sa dim L h
  match vf with
  | Eq.refl _ => Eq.trans vb inv

theorem backwardVectorizedCore_round_trip (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h : L.length = dim + dim) :
  forwardVectorizedCore sa dim (backwardVectorizedCore sa dim L) = L :=
  let vb := backwardVectorizedCore_eq_core sa dim L h
  let hlen : (backwardCore sa dim L).length = dim + dim := length_backwardCore sa dim L h
  let vf := forwardVectorizedCore_eq_core sa dim (backwardCore sa dim L) hlen
  let inv := oftb_invertible_rev sa dim L h
  match vb with
  | Eq.refl _ => Eq.trans vf inv

theorem forwardVectorizedPairList_first_block_exact (sa : ScaleAlgebra F)
  (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : F)
  (as bs : List F) :
  (forwardVectorizedPairList sa
    (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: as)
    (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs)).1 =
    scalarForwardExpr sa a0 b0 :: scalarForwardExpr sa a1 b1 ::
    scalarForwardExpr sa a2 b2 :: scalarForwardExpr sa a3 b3 ::
    scalarForwardExpr sa a4 b4 :: scalarForwardExpr sa a5 b5 ::
    scalarForwardExpr sa a6 b6 :: scalarForwardExpr sa a7 b7 ::
    (forwardVectorizedPairList sa as bs).1 :=
  Eq.refl _

theorem forwardVectorizedPairList_second_block_exact (sa : ScaleAlgebra F)
  (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : F)
  (as bs : List F) :
  (forwardVectorizedPairList sa
    (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: as)
    (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs)).2 =
    scalarForwardExpr2 sa a0 b0 :: scalarForwardExpr2 sa a1 b1 ::
    scalarForwardExpr2 sa a2 b2 :: scalarForwardExpr2 sa a3 b3 ::
    scalarForwardExpr2 sa a4 b4 :: scalarForwardExpr2 sa a5 b5 ::
    scalarForwardExpr2 sa a6 b6 :: scalarForwardExpr2 sa a7 b7 ::
    (forwardVectorizedPairList sa as bs).2 :=
  Eq.refl _

theorem backwardVectorizedPairList_first_block_exact (sa : ScaleAlgebra F)
  (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : F)
  (as bs : List F) :
  (backwardVectorizedPairList sa
    (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: as)
    (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs)).1 =
    scalarBackwardExpr1 sa a0 b0 :: scalarBackwardExpr1 sa a1 b1 ::
    scalarBackwardExpr1 sa a2 b2 :: scalarBackwardExpr1 sa a3 b3 ::
    scalarBackwardExpr1 sa a4 b4 :: scalarBackwardExpr1 sa a5 b5 ::
    scalarBackwardExpr1 sa a6 b6 :: scalarBackwardExpr1 sa a7 b7 ::
    (backwardVectorizedPairList sa as bs).1 :=
  Eq.refl _

theorem backwardVectorizedPairList_second_block_exact (sa : ScaleAlgebra F)
  (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : F)
  (as bs : List F) :
  (backwardVectorizedPairList sa
    (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: as)
    (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs)).2 =
    scalarBackwardExpr2 sa a0 b0 :: scalarBackwardExpr2 sa a1 b1 ::
    scalarBackwardExpr2 sa a2 b2 :: scalarBackwardExpr2 sa a3 b3 ::
    scalarBackwardExpr2 sa a4 b4 :: scalarBackwardExpr2 sa a5 b5 ::
    scalarBackwardExpr2 sa a6 b6 :: scalarBackwardExpr2 sa a7 b7 ::
    (backwardVectorizedPairList sa as bs).2 :=
  Eq.refl _

end ZigOFTBSemantics

namespace ZigOFTBDeepArchitecture

open ZigOFTBSemantics

structure Vec8 (F : Type) where
  lane0 : F
  lane1 : F
  lane2 : F
  lane3 : F
  lane4 : F
  lane5 : F
  lane6 : F
  lane7 : F

def vec8ForwardLeft (sa : ScaleAlgebra F) (a b : Vec8 F) : Vec8 F :=
  { lane0 := scalarForwardExpr sa a.lane0 b.lane0,
    lane1 := scalarForwardExpr sa a.lane1 b.lane1,
    lane2 := scalarForwardExpr sa a.lane2 b.lane2,
    lane3 := scalarForwardExpr sa a.lane3 b.lane3,
    lane4 := scalarForwardExpr sa a.lane4 b.lane4,
    lane5 := scalarForwardExpr sa a.lane5 b.lane5,
    lane6 := scalarForwardExpr sa a.lane6 b.lane6,
    lane7 := scalarForwardExpr sa a.lane7 b.lane7 }

def vec8ForwardRight (sa : ScaleAlgebra F) (a b : Vec8 F) : Vec8 F :=
  { lane0 := scalarForwardExpr2 sa a.lane0 b.lane0,
    lane1 := scalarForwardExpr2 sa a.lane1 b.lane1,
    lane2 := scalarForwardExpr2 sa a.lane2 b.lane2,
    lane3 := scalarForwardExpr2 sa a.lane3 b.lane3,
    lane4 := scalarForwardExpr2 sa a.lane4 b.lane4,
    lane5 := scalarForwardExpr2 sa a.lane5 b.lane5,
    lane6 := scalarForwardExpr2 sa a.lane6 b.lane6,
    lane7 := scalarForwardExpr2 sa a.lane7 b.lane7 }

def vec8BackwardLeft (sa : ScaleAlgebra F) (a b : Vec8 F) : Vec8 F :=
  { lane0 := scalarBackwardExpr1 sa a.lane0 b.lane0,
    lane1 := scalarBackwardExpr1 sa a.lane1 b.lane1,
    lane2 := scalarBackwardExpr1 sa a.lane2 b.lane2,
    lane3 := scalarBackwardExpr1 sa a.lane3 b.lane3,
    lane4 := scalarBackwardExpr1 sa a.lane4 b.lane4,
    lane5 := scalarBackwardExpr1 sa a.lane5 b.lane5,
    lane6 := scalarBackwardExpr1 sa a.lane6 b.lane6,
    lane7 := scalarBackwardExpr1 sa a.lane7 b.lane7 }

def vec8BackwardRight (sa : ScaleAlgebra F) (a b : Vec8 F) : Vec8 F :=
  { lane0 := scalarBackwardExpr2 sa a.lane0 b.lane0,
    lane1 := scalarBackwardExpr2 sa a.lane1 b.lane1,
    lane2 := scalarBackwardExpr2 sa a.lane2 b.lane2,
    lane3 := scalarBackwardExpr2 sa a.lane3 b.lane3,
    lane4 := scalarBackwardExpr2 sa a.lane4 b.lane4,
    lane5 := scalarBackwardExpr2 sa a.lane5 b.lane5,
    lane6 := scalarBackwardExpr2 sa a.lane6 b.lane6,
    lane7 := scalarBackwardExpr2 sa a.lane7 b.lane7 }

def vec8ToList (v : Vec8 F) : List F :=
  v.lane0 :: v.lane1 :: v.lane2 :: v.lane3 ::
  v.lane4 :: v.lane5 :: v.lane6 :: v.lane7 :: []

def vec8ForwardBlock (sa : ScaleAlgebra F) (a b : Vec8 F) : Vec8 F × Vec8 F :=
  (vec8ForwardLeft sa a b, vec8ForwardRight sa a b)

def vec8BackwardBlock (sa : ScaleAlgebra F) (a b : Vec8 F) : Vec8 F × Vec8 F :=
  (vec8BackwardLeft sa a b, vec8BackwardRight sa a b)

def forwardReadBeforeWritePair (sa : ScaleAlgebra F) (a b : F) : F × F :=
  let old_a := a
  let old_b := b
  let left_write := scalarForwardExpr sa old_a old_b
  let right_write := scalarForwardExpr2 sa old_a old_b
  (left_write, right_write)

def backwardReadBeforeWritePair (sa : ScaleAlgebra F) (a b : F) : F × F :=
  let old_a := a
  let old_b := b
  let left_write := scalarBackwardExpr1 sa old_a old_b
  let right_write := scalarBackwardExpr2 sa old_a old_b
  (left_write, right_write)

theorem forward_read_before_write_pair_exact (sa : ScaleAlgebra F) (a b : F) :
  forwardReadBeforeWritePair sa a b = forwardPair sa a b :=
  Eq.refl _

theorem backward_read_before_write_pair_exact (sa : ScaleAlgebra F) (a b : F) :
  backwardReadBeforeWritePair sa a b = backwardPair sa a b :=
  Eq.refl _

theorem vec8_forward_left_list_exact (sa : ScaleAlgebra F) (a b : Vec8 F) :
  vec8ToList (vec8ForwardLeft sa a b) =
    scalarForwardExpr sa a.lane0 b.lane0 ::
    scalarForwardExpr sa a.lane1 b.lane1 ::
    scalarForwardExpr sa a.lane2 b.lane2 ::
    scalarForwardExpr sa a.lane3 b.lane3 ::
    scalarForwardExpr sa a.lane4 b.lane4 ::
    scalarForwardExpr sa a.lane5 b.lane5 ::
    scalarForwardExpr sa a.lane6 b.lane6 ::
    scalarForwardExpr sa a.lane7 b.lane7 :: [] :=
  Eq.refl _

theorem vec8_forward_right_list_exact (sa : ScaleAlgebra F) (a b : Vec8 F) :
  vec8ToList (vec8ForwardRight sa a b) =
    scalarForwardExpr2 sa a.lane0 b.lane0 ::
    scalarForwardExpr2 sa a.lane1 b.lane1 ::
    scalarForwardExpr2 sa a.lane2 b.lane2 ::
    scalarForwardExpr2 sa a.lane3 b.lane3 ::
    scalarForwardExpr2 sa a.lane4 b.lane4 ::
    scalarForwardExpr2 sa a.lane5 b.lane5 ::
    scalarForwardExpr2 sa a.lane6 b.lane6 ::
    scalarForwardExpr2 sa a.lane7 b.lane7 :: [] :=
  Eq.refl _

theorem vec8_backward_left_list_exact (sa : ScaleAlgebra F) (a b : Vec8 F) :
  vec8ToList (vec8BackwardLeft sa a b) =
    scalarBackwardExpr1 sa a.lane0 b.lane0 ::
    scalarBackwardExpr1 sa a.lane1 b.lane1 ::
    scalarBackwardExpr1 sa a.lane2 b.lane2 ::
    scalarBackwardExpr1 sa a.lane3 b.lane3 ::
    scalarBackwardExpr1 sa a.lane4 b.lane4 ::
    scalarBackwardExpr1 sa a.lane5 b.lane5 ::
    scalarBackwardExpr1 sa a.lane6 b.lane6 ::
    scalarBackwardExpr1 sa a.lane7 b.lane7 :: [] :=
  Eq.refl _

theorem vec8_backward_right_list_exact (sa : ScaleAlgebra F) (a b : Vec8 F) :
  vec8ToList (vec8BackwardRight sa a b) =
    scalarBackwardExpr2 sa a.lane0 b.lane0 ::
    scalarBackwardExpr2 sa a.lane1 b.lane1 ::
    scalarBackwardExpr2 sa a.lane2 b.lane2 ::
    scalarBackwardExpr2 sa a.lane3 b.lane3 ::
    scalarBackwardExpr2 sa a.lane4 b.lane4 ::
    scalarBackwardExpr2 sa a.lane5 b.lane5 ::
    scalarBackwardExpr2 sa a.lane6 b.lane6 ::
    scalarBackwardExpr2 sa a.lane7 b.lane7 :: [] :=
  Eq.refl _

theorem vec8_forward_then_backward_left_lanes (sa : ScaleAlgebra F) (a b : Vec8 F) :
  let fl := vec8ForwardLeft sa a b
  let fr := vec8ForwardRight sa a b
  scalarBackwardExpr1 sa fl.lane0 fr.lane0 = a.lane0 ∧
  scalarBackwardExpr1 sa fl.lane1 fr.lane1 = a.lane1 ∧
  scalarBackwardExpr1 sa fl.lane2 fr.lane2 = a.lane2 ∧
  scalarBackwardExpr1 sa fl.lane3 fr.lane3 = a.lane3 ∧
  scalarBackwardExpr1 sa fl.lane4 fr.lane4 = a.lane4 ∧
  scalarBackwardExpr1 sa fl.lane5 fr.lane5 = a.lane5 ∧
  scalarBackwardExpr1 sa fl.lane6 fr.lane6 = a.lane6 ∧
  scalarBackwardExpr1 sa fl.lane7 fr.lane7 = a.lane7 :=
  And.intro (first_component_proof sa a.lane0 b.lane0)
  (And.intro (first_component_proof sa a.lane1 b.lane1)
  (And.intro (first_component_proof sa a.lane2 b.lane2)
  (And.intro (first_component_proof sa a.lane3 b.lane3)
  (And.intro (first_component_proof sa a.lane4 b.lane4)
  (And.intro (first_component_proof sa a.lane5 b.lane5)
  (And.intro (first_component_proof sa a.lane6 b.lane6)
             (first_component_proof sa a.lane7 b.lane7)))))))

theorem vec8_forward_then_backward_right_lanes (sa : ScaleAlgebra F) (a b : Vec8 F) :
  let fl := vec8ForwardLeft sa a b
  let fr := vec8ForwardRight sa a b
  scalarBackwardExpr2 sa fl.lane0 fr.lane0 = b.lane0 ∧
  scalarBackwardExpr2 sa fl.lane1 fr.lane1 = b.lane1 ∧
  scalarBackwardExpr2 sa fl.lane2 fr.lane2 = b.lane2 ∧
  scalarBackwardExpr2 sa fl.lane3 fr.lane3 = b.lane3 ∧
  scalarBackwardExpr2 sa fl.lane4 fr.lane4 = b.lane4 ∧
  scalarBackwardExpr2 sa fl.lane5 fr.lane5 = b.lane5 ∧
  scalarBackwardExpr2 sa fl.lane6 fr.lane6 = b.lane6 ∧
  scalarBackwardExpr2 sa fl.lane7 fr.lane7 = b.lane7 :=
  And.intro (second_component_proof sa a.lane0 b.lane0)
  (And.intro (second_component_proof sa a.lane1 b.lane1)
  (And.intro (second_component_proof sa a.lane2 b.lane2)
  (And.intro (second_component_proof sa a.lane3 b.lane3)
  (And.intro (second_component_proof sa a.lane4 b.lane4)
  (And.intro (second_component_proof sa a.lane5 b.lane5)
  (And.intro (second_component_proof sa a.lane6 b.lane6)
             (second_component_proof sa a.lane7 b.lane7)))))))

theorem vec8_backward_then_forward_left_lanes (sa : ScaleAlgebra F) (a b : Vec8 F) :
  let bl := vec8BackwardLeft sa a b
  let br := vec8BackwardRight sa a b
  scalarForwardExpr sa bl.lane0 br.lane0 = a.lane0 ∧
  scalarForwardExpr sa bl.lane1 br.lane1 = a.lane1 ∧
  scalarForwardExpr sa bl.lane2 br.lane2 = a.lane2 ∧
  scalarForwardExpr sa bl.lane3 br.lane3 = a.lane3 ∧
  scalarForwardExpr sa bl.lane4 br.lane4 = a.lane4 ∧
  scalarForwardExpr sa bl.lane5 br.lane5 = a.lane5 ∧
  scalarForwardExpr sa bl.lane6 br.lane6 = a.lane6 ∧
  scalarForwardExpr sa bl.lane7 br.lane7 = a.lane7 :=
  And.intro (first_component_proof_rev sa a.lane0 b.lane0)
  (And.intro (first_component_proof_rev sa a.lane1 b.lane1)
  (And.intro (first_component_proof_rev sa a.lane2 b.lane2)
  (And.intro (first_component_proof_rev sa a.lane3 b.lane3)
  (And.intro (first_component_proof_rev sa a.lane4 b.lane4)
  (And.intro (first_component_proof_rev sa a.lane5 b.lane5)
  (And.intro (first_component_proof_rev sa a.lane6 b.lane6)
             (first_component_proof_rev sa a.lane7 b.lane7)))))))

theorem vec8_backward_then_forward_right_lanes (sa : ScaleAlgebra F) (a b : Vec8 F) :
  let bl := vec8BackwardLeft sa a b
  let br := vec8BackwardRight sa a b
  scalarForwardExpr2 sa bl.lane0 br.lane0 = b.lane0 ∧
  scalarForwardExpr2 sa bl.lane1 br.lane1 = b.lane1 ∧
  scalarForwardExpr2 sa bl.lane2 br.lane2 = b.lane2 ∧
  scalarForwardExpr2 sa bl.lane3 br.lane3 = b.lane3 ∧
  scalarForwardExpr2 sa bl.lane4 br.lane4 = b.lane4 ∧
  scalarForwardExpr2 sa bl.lane5 br.lane5 = b.lane5 ∧
  scalarForwardExpr2 sa bl.lane6 br.lane6 = b.lane6 ∧
  scalarForwardExpr2 sa bl.lane7 br.lane7 = b.lane7 :=
  And.intro (second_component_proof_rev sa a.lane0 b.lane0)
  (And.intro (second_component_proof_rev sa a.lane1 b.lane1)
  (And.intro (second_component_proof_rev sa a.lane2 b.lane2)
  (And.intro (second_component_proof_rev sa a.lane3 b.lane3)
  (And.intro (second_component_proof_rev sa a.lane4 b.lane4)
  (And.intro (second_component_proof_rev sa a.lane5 b.lane5)
  (And.intro (second_component_proof_rev sa a.lane6 b.lane6)
             (second_component_proof_rev sa a.lane7 b.lane7)))))))

def eightStepForwardHeadList (sa : ScaleAlgebra F)
  (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : F) : List F × List F :=
  (scalarForwardExpr sa a0 b0 :: scalarForwardExpr sa a1 b1 ::
   scalarForwardExpr sa a2 b2 :: scalarForwardExpr sa a3 b3 ::
   scalarForwardExpr sa a4 b4 :: scalarForwardExpr sa a5 b5 ::
   scalarForwardExpr sa a6 b6 :: scalarForwardExpr sa a7 b7 :: [],
   scalarForwardExpr2 sa a0 b0 :: scalarForwardExpr2 sa a1 b1 ::
   scalarForwardExpr2 sa a2 b2 :: scalarForwardExpr2 sa a3 b3 ::
   scalarForwardExpr2 sa a4 b4 :: scalarForwardExpr2 sa a5 b5 ::
   scalarForwardExpr2 sa a6 b6 :: scalarForwardExpr2 sa a7 b7 :: [])

def eightStepBackwardHeadList (sa : ScaleAlgebra F)
  (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : F) : List F × List F :=
  (scalarBackwardExpr1 sa a0 b0 :: scalarBackwardExpr1 sa a1 b1 ::
   scalarBackwardExpr1 sa a2 b2 :: scalarBackwardExpr1 sa a3 b3 ::
   scalarBackwardExpr1 sa a4 b4 :: scalarBackwardExpr1 sa a5 b5 ::
   scalarBackwardExpr1 sa a6 b6 :: scalarBackwardExpr1 sa a7 b7 :: [],
   scalarBackwardExpr2 sa a0 b0 :: scalarBackwardExpr2 sa a1 b1 ::
   scalarBackwardExpr2 sa a2 b2 :: scalarBackwardExpr2 sa a3 b3 ::
   scalarBackwardExpr2 sa a4 b4 :: scalarBackwardExpr2 sa a5 b5 ::
   scalarBackwardExpr2 sa a6 b6 :: scalarBackwardExpr2 sa a7 b7 :: [])

theorem vectorized_forward_head_then_tail_exact (sa : ScaleAlgebra F)
  (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : F)
  (as bs : List F) :
  forwardVectorizedPairList sa
    (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: as)
    (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs) =
  let head := eightStepForwardHeadList sa a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7
  let tail := forwardVectorizedPairList sa as bs
  (head.1 ++ tail.1, head.2 ++ tail.2) :=
  Eq.refl _

theorem vectorized_backward_head_then_tail_exact (sa : ScaleAlgebra F)
  (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : F)
  (as bs : List F) :
  backwardVectorizedPairList sa
    (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: as)
    (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs) =
  let head := eightStepBackwardHeadList sa a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7
  let tail := backwardVectorizedPairList sa as bs
  (head.1 ++ tail.1, head.2 ++ tail.2) :=
  Eq.refl _

theorem vector_path_public_forward_exact (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h : L.length = dim + dim) :
  forwardChecked sa dim L = ZigResult.ok (forwardVectorizedCore sa dim L) ∨
  forwardChecked sa dim L = ZigResult.err ZigError.InvalidDimension ∨
  forwardChecked sa dim L = ZigResult.err ZigError.DimensionOverflow ∨
  forwardChecked sa dim L = ZigResult.err ZigError.DimensionMismatch :=
  match dim with
  | 0 => Or.inr (Or.inl (Eq.refl _))
  | Nat.succ k =>
    match Nat.decLt usizeHalf (Nat.succ k) with
    | Decidable.isTrue _ => Or.inr (Or.inr (Or.inl (Eq.refl _)))
    | Decidable.isFalse hn =>
      let h0 : Not (Nat.succ k = 0) := succ_not_zero k
      let hs := forward_checked_success sa (Nat.succ k) L h0 hn h
      let hv := Eq.symm (forwardVectorizedCore_eq_core sa (Nat.succ k) L h)
      let hok : ZigResult.ok (forwardCore sa (Nat.succ k) L) = ZigResult.ok (forwardVectorizedCore sa (Nat.succ k) L) := congrArg ZigResult.ok hv
      Or.inl (Eq.trans hs hok)

theorem vector_path_public_backward_exact (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h : L.length = dim + dim) :
  backwardChecked sa dim L = ZigResult.ok (backwardVectorizedCore sa dim L) ∨
  backwardChecked sa dim L = ZigResult.err ZigError.InvalidDimension ∨
  backwardChecked sa dim L = ZigResult.err ZigError.DimensionOverflow ∨
  backwardChecked sa dim L = ZigResult.err ZigError.DimensionMismatch :=
  match dim with
  | 0 => Or.inr (Or.inl (Eq.refl _))
  | Nat.succ k =>
    match Nat.decLt usizeHalf (Nat.succ k) with
    | Decidable.isTrue _ => Or.inr (Or.inr (Or.inl (Eq.refl _)))
    | Decidable.isFalse hn =>
      let h0 : Not (Nat.succ k = 0) := succ_not_zero k
      let hs := backward_checked_success sa (Nat.succ k) L h0 hn h
      let hv := Eq.symm (backwardVectorizedCore_eq_core sa (Nat.succ k) L h)
      let hok : ZigResult.ok (backwardCore sa (Nat.succ k) L) = ZigResult.ok (backwardVectorizedCore sa (Nat.succ k) L) := congrArg ZigResult.ok hv
      Or.inl (Eq.trans hs hok)

end ZigOFTBDeepArchitecture

namespace ZigOFTBDeepArchitecture

open ZigOFTBSemantics

def pair_eq {α β : Type} {a c : α} {b d : β} (h1 : a = c) (h2 : b = d) :
  (a, b) = (c, d) :=
  match h1, h2 with
  | Eq.refl _, Eq.refl _ => Eq.refl _

def vec8_ext {x y : Vec8 F}
  (h0 : x.lane0 = y.lane0)
  (h1 : x.lane1 = y.lane1)
  (h2 : x.lane2 = y.lane2)
  (h3 : x.lane3 = y.lane3)
  (h4 : x.lane4 = y.lane4)
  (h5 : x.lane5 = y.lane5)
  (h6 : x.lane6 = y.lane6)
  (h7 : x.lane7 = y.lane7) : x = y :=
  match x, y with
  | ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩,
    ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ =>
    match h0, h1, h2, h3, h4, h5, h6, h7 with
    | Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _ => Eq.refl _

def ForwardBlockPost (sa : ScaleAlgebra F) (oldL oldR newL newR : Vec8 F) : Prop :=
  newL = vec8ForwardLeft sa oldL oldR ∧
  newR = vec8ForwardRight sa oldL oldR

def BackwardBlockPost (sa : ScaleAlgebra F) (oldL oldR newL newR : Vec8 F) : Prop :=
  newL = vec8BackwardLeft sa oldL oldR ∧
  newR = vec8BackwardRight sa oldL oldR

structure InPlaceBlockState (F : Type) where
  left : Vec8 F
  right : Vec8 F

def forwardBlockInPlaceState (sa : ScaleAlgebra F) (s : InPlaceBlockState F) : InPlaceBlockState F :=
  let va := s.left
  let vb := s.right
  { left := vec8ForwardLeft sa va vb,
    right := vec8ForwardRight sa va vb }

def backwardBlockInPlaceState (sa : ScaleAlgebra F) (s : InPlaceBlockState F) : InPlaceBlockState F :=
  let va := s.left
  let vb := s.right
  { left := vec8BackwardLeft sa va vb,
    right := vec8BackwardRight sa va vb }

theorem forward_block_post_exact (sa : ScaleAlgebra F) (s : InPlaceBlockState F) :
  ForwardBlockPost sa s.left s.right (forwardBlockInPlaceState sa s).left (forwardBlockInPlaceState sa s).right :=
  And.intro (Eq.refl _) (Eq.refl _)

theorem backward_block_post_exact (sa : ScaleAlgebra F) (s : InPlaceBlockState F) :
  BackwardBlockPost sa s.left s.right (backwardBlockInPlaceState sa s).left (backwardBlockInPlaceState sa s).right :=
  And.intro (Eq.refl _) (Eq.refl _)

theorem vec8_forward_backward_left_exact (sa : ScaleAlgebra F) (a b : Vec8 F) :
  vec8BackwardLeft sa (vec8ForwardLeft sa a b) (vec8ForwardRight sa a b) = a :=
  vec8_ext
    (first_component_proof sa a.lane0 b.lane0)
    (first_component_proof sa a.lane1 b.lane1)
    (first_component_proof sa a.lane2 b.lane2)
    (first_component_proof sa a.lane3 b.lane3)
    (first_component_proof sa a.lane4 b.lane4)
    (first_component_proof sa a.lane5 b.lane5)
    (first_component_proof sa a.lane6 b.lane6)
    (first_component_proof sa a.lane7 b.lane7)

theorem vec8_forward_backward_right_exact (sa : ScaleAlgebra F) (a b : Vec8 F) :
  vec8BackwardRight sa (vec8ForwardLeft sa a b) (vec8ForwardRight sa a b) = b :=
  vec8_ext
    (second_component_proof sa a.lane0 b.lane0)
    (second_component_proof sa a.lane1 b.lane1)
    (second_component_proof sa a.lane2 b.lane2)
    (second_component_proof sa a.lane3 b.lane3)
    (second_component_proof sa a.lane4 b.lane4)
    (second_component_proof sa a.lane5 b.lane5)
    (second_component_proof sa a.lane6 b.lane6)
    (second_component_proof sa a.lane7 b.lane7)

theorem vec8_backward_forward_left_exact (sa : ScaleAlgebra F) (a b : Vec8 F) :
  vec8ForwardLeft sa (vec8BackwardLeft sa a b) (vec8BackwardRight sa a b) = a :=
  vec8_ext
    (first_component_proof_rev sa a.lane0 b.lane0)
    (first_component_proof_rev sa a.lane1 b.lane1)
    (first_component_proof_rev sa a.lane2 b.lane2)
    (first_component_proof_rev sa a.lane3 b.lane3)
    (first_component_proof_rev sa a.lane4 b.lane4)
    (first_component_proof_rev sa a.lane5 b.lane5)
    (first_component_proof_rev sa a.lane6 b.lane6)
    (first_component_proof_rev sa a.lane7 b.lane7)

theorem vec8_backward_forward_right_exact (sa : ScaleAlgebra F) (a b : Vec8 F) :
  vec8ForwardRight sa (vec8BackwardLeft sa a b) (vec8BackwardRight sa a b) = b :=
  vec8_ext
    (second_component_proof_rev sa a.lane0 b.lane0)
    (second_component_proof_rev sa a.lane1 b.lane1)
    (second_component_proof_rev sa a.lane2 b.lane2)
    (second_component_proof_rev sa a.lane3 b.lane3)
    (second_component_proof_rev sa a.lane4 b.lane4)
    (second_component_proof_rev sa a.lane5 b.lane5)
    (second_component_proof_rev sa a.lane6 b.lane6)
    (second_component_proof_rev sa a.lane7 b.lane7)

theorem vec8_forward_block_inverse_exact (sa : ScaleAlgebra F) (a b : Vec8 F) :
  let p := vec8ForwardBlock sa a b
  vec8BackwardBlock sa p.1 p.2 = (a, b) :=
  pair_eq
    (vec8_forward_backward_left_exact sa a b)
    (vec8_forward_backward_right_exact sa a b)

theorem vec8_backward_block_inverse_exact (sa : ScaleAlgebra F) (a b : Vec8 F) :
  let p := vec8BackwardBlock sa a b
  vec8ForwardBlock sa p.1 p.2 = (a, b) :=
  pair_eq
    (vec8_backward_forward_left_exact sa a b)
    (vec8_backward_forward_right_exact sa a b)

theorem in_place_block_forward_backward_exact (sa : ScaleAlgebra F) (s : InPlaceBlockState F) :
  backwardBlockInPlaceState sa (forwardBlockInPlaceState sa s) = s :=
  match s with
  | ⟨l, r⟩ =>
    let hl := vec8_forward_backward_left_exact sa l r
    let hr := vec8_forward_backward_right_exact sa l r
    match hl, hr with
    | Eq.refl _, Eq.refl _ => Eq.refl _

theorem in_place_block_backward_forward_exact (sa : ScaleAlgebra F) (s : InPlaceBlockState F) :
  forwardBlockInPlaceState sa (backwardBlockInPlaceState sa s) = s :=
  match s with
  | ⟨l, r⟩ =>
    let hl := vec8_backward_forward_left_exact sa l r
    let hr := vec8_backward_forward_right_exact sa l r
    match hl, hr with
    | Eq.refl _, Eq.refl _ => Eq.refl _

def LanePairForwardBackwardInvariant (sa : ScaleAlgebra F) (a b : F) : Prop :=
  let u := scalarForwardExpr sa a b
  let v := scalarForwardExpr2 sa a b
  scalarBackwardExpr1 sa u v = a ∧ scalarBackwardExpr2 sa u v = b

def LanePairBackwardForwardInvariant (sa : ScaleAlgebra F) (a b : F) : Prop :=
  let u := scalarBackwardExpr1 sa a b
  let v := scalarBackwardExpr2 sa a b
  scalarForwardExpr sa u v = a ∧ scalarForwardExpr2 sa u v = b

theorem lane_pair_forward_backward_invariant_exact (sa : ScaleAlgebra F) (a b : F) :
  LanePairForwardBackwardInvariant sa a b :=
  And.intro (first_component_proof sa a b) (second_component_proof sa a b)

theorem lane_pair_backward_forward_invariant_exact (sa : ScaleAlgebra F) (a b : F) :
  LanePairBackwardForwardInvariant sa a b :=
  And.intro (first_component_proof_rev sa a b) (second_component_proof_rev sa a b)

def Vec8ForwardBackwardInvariant (sa : ScaleAlgebra F) (a b : Vec8 F) : Prop :=
  LanePairForwardBackwardInvariant sa a.lane0 b.lane0 ∧
  LanePairForwardBackwardInvariant sa a.lane1 b.lane1 ∧
  LanePairForwardBackwardInvariant sa a.lane2 b.lane2 ∧
  LanePairForwardBackwardInvariant sa a.lane3 b.lane3 ∧
  LanePairForwardBackwardInvariant sa a.lane4 b.lane4 ∧
  LanePairForwardBackwardInvariant sa a.lane5 b.lane5 ∧
  LanePairForwardBackwardInvariant sa a.lane6 b.lane6 ∧
  LanePairForwardBackwardInvariant sa a.lane7 b.lane7

def Vec8BackwardForwardInvariant (sa : ScaleAlgebra F) (a b : Vec8 F) : Prop :=
  LanePairBackwardForwardInvariant sa a.lane0 b.lane0 ∧
  LanePairBackwardForwardInvariant sa a.lane1 b.lane1 ∧
  LanePairBackwardForwardInvariant sa a.lane2 b.lane2 ∧
  LanePairBackwardForwardInvariant sa a.lane3 b.lane3 ∧
  LanePairBackwardForwardInvariant sa a.lane4 b.lane4 ∧
  LanePairBackwardForwardInvariant sa a.lane5 b.lane5 ∧
  LanePairBackwardForwardInvariant sa a.lane6 b.lane6 ∧
  LanePairBackwardForwardInvariant sa a.lane7 b.lane7

theorem vec8_forward_backward_invariant_exact (sa : ScaleAlgebra F) (a b : Vec8 F) :
  Vec8ForwardBackwardInvariant sa a b :=
  And.intro (lane_pair_forward_backward_invariant_exact sa a.lane0 b.lane0)
  (And.intro (lane_pair_forward_backward_invariant_exact sa a.lane1 b.lane1)
  (And.intro (lane_pair_forward_backward_invariant_exact sa a.lane2 b.lane2)
  (And.intro (lane_pair_forward_backward_invariant_exact sa a.lane3 b.lane3)
  (And.intro (lane_pair_forward_backward_invariant_exact sa a.lane4 b.lane4)
  (And.intro (lane_pair_forward_backward_invariant_exact sa a.lane5 b.lane5)
  (And.intro (lane_pair_forward_backward_invariant_exact sa a.lane6 b.lane6)
             (lane_pair_forward_backward_invariant_exact sa a.lane7 b.lane7)))))))

theorem vec8_backward_forward_invariant_exact (sa : ScaleAlgebra F) (a b : Vec8 F) :
  Vec8BackwardForwardInvariant sa a b :=
  And.intro (lane_pair_backward_forward_invariant_exact sa a.lane0 b.lane0)
  (And.intro (lane_pair_backward_forward_invariant_exact sa a.lane1 b.lane1)
  (And.intro (lane_pair_backward_forward_invariant_exact sa a.lane2 b.lane2)
  (And.intro (lane_pair_backward_forward_invariant_exact sa a.lane3 b.lane3)
  (And.intro (lane_pair_backward_forward_invariant_exact sa a.lane4 b.lane4)
  (And.intro (lane_pair_backward_forward_invariant_exact sa a.lane5 b.lane5)
  (And.intro (lane_pair_backward_forward_invariant_exact sa a.lane6 b.lane6)
             (lane_pair_backward_forward_invariant_exact sa a.lane7 b.lane7)))))))

def loopBoundSafe (i half : Nat) : Prop :=
  i + VLEN ≤ half

def loopRemainderReached (i half : Nat) : Prop :=
  Not (i + VLEN ≤ half)

def vectorLoopCondition (i half : Nat) : Bool :=
  match Nat.decLe (i + VLEN) half with
  | Decidable.isTrue _ => Bool.true
  | Decidable.isFalse _ => Bool.false

theorem vector_loop_condition_true_exact (i half : Nat) (h : i + VLEN ≤ half) :
  vectorLoopCondition i half = Bool.true :=
  match Nat.decLe (i + VLEN) half with
  | Decidable.isTrue _ => Eq.refl _
  | Decidable.isFalse hn => False.elim (hn h)

theorem vector_loop_condition_false_exact (i half : Nat) (h : Not (i + VLEN ≤ half)) :
  vectorLoopCondition i half = Bool.false :=
  match Nat.decLe (i + VLEN) half with
  | Decidable.isTrue hp => False.elim (h hp)
  | Decidable.isFalse _ => Eq.refl _

theorem vector_loop_true_means_safe (i half : Nat) (h : vectorLoopCondition i half = Bool.true) :
  loopBoundSafe i half :=
  match Nat.decLe (i + VLEN) half with
  | Decidable.isTrue hp => hp
  | Decidable.isFalse _ => nomatch h

theorem vector_loop_false_means_remainder (i half : Nat) (h : vectorLoopCondition i half = Bool.false) :
  loopRemainderReached i half :=
  match Nat.decLe (i + VLEN) half with
  | Decidable.isTrue _ => nomatch h
  | Decidable.isFalse hn => hn

end ZigOFTBDeepArchitecture

namespace ZigOFTBDeepArchitecture

open ZigOFTBSemantics

structure SliceView where
  start : Nat
  len : Nat

structure OFTBSliceLayout where
  left : SliceView
  right : SliceView
  total : Nat

def leftSlice (dim : Nat) : SliceView :=
  { start := 0, len := dim }

def rightSlice (dim : Nat) : SliceView :=
  { start := dim, len := dim }

def oftbSliceLayout (dim : Nat) : OFTBSliceLayout :=
  { left := leftSlice dim,
    right := rightSlice dim,
    total := dim + dim }

def sliceEnd (s : SliceView) : Nat :=
  s.start + s.len

def sliceInBounds (s : SliceView) (total : Nat) : Prop :=
  sliceEnd s ≤ total

def slicesDisjoint (a b : SliceView) : Prop :=
  sliceEnd a ≤ b.start ∨ sliceEnd b ≤ a.start

def slicesAdjacent (a b : SliceView) : Prop :=
  sliceEnd a = b.start

def slicesCoverOFTB (dim : Nat) (layout : OFTBSliceLayout) : Prop :=
  layout.left.start = 0 ∧
  layout.left.len = dim ∧
  layout.right.start = dim ∧
  layout.right.len = dim ∧
  layout.total = dim + dim ∧
  slicesAdjacent layout.left layout.right ∧
  sliceInBounds layout.left layout.total ∧
  sliceInBounds layout.right layout.total ∧
  slicesDisjoint layout.left layout.right

theorem nat_le_self_add_right_deep : (n m : Nat) → n ≤ n + m
| 0, m => Nat.zero_le m
| Nat.succ n, m => Nat.succ_le_succ (nat_le_self_add_right_deep n m)

theorem left_slice_start_exact (dim : Nat) :
  (leftSlice dim).start = 0 :=
  Eq.refl 0

theorem left_slice_len_exact (dim : Nat) :
  (leftSlice dim).len = dim :=
  Eq.refl dim

theorem right_slice_start_exact (dim : Nat) :
  (rightSlice dim).start = dim :=
  Eq.refl dim

theorem right_slice_len_exact (dim : Nat) :
  (rightSlice dim).len = dim :=
  Eq.refl dim

theorem left_slice_end_exact (dim : Nat) :
  sliceEnd (leftSlice dim) = dim :=
  Eq.refl dim

theorem right_slice_end_exact (dim : Nat) :
  sliceEnd (rightSlice dim) = dim + dim :=
  Eq.refl (dim + dim)

theorem oftb_slices_adjacent_exact (dim : Nat) :
  slicesAdjacent (leftSlice dim) (rightSlice dim) :=
  Eq.refl dim

theorem oftb_left_slice_in_bounds (dim : Nat) :
  sliceInBounds (leftSlice dim) (dim + dim) :=
  nat_le_self_add_right_deep dim dim

theorem oftb_right_slice_in_bounds (dim : Nat) :
  sliceInBounds (rightSlice dim) (dim + dim) :=
  Nat.le_refl (dim + dim)

theorem oftb_slices_disjoint_exact (dim : Nat) :
  slicesDisjoint (leftSlice dim) (rightSlice dim) :=
  Or.inl (Nat.le_refl dim)

theorem oftb_layout_covers_exact (dim : Nat) :
  slicesCoverOFTB dim (oftbSliceLayout dim) :=
  And.intro (Eq.refl 0)
  (And.intro (Eq.refl dim)
  (And.intro (Eq.refl dim)
  (And.intro (Eq.refl dim)
  (And.intro (Eq.refl (dim + dim))
  (And.intro (oftb_slices_adjacent_exact dim)
  (And.intro (oftb_left_slice_in_bounds dim)
  (And.intro (oftb_right_slice_in_bounds dim)
             (oftb_slices_disjoint_exact dim))))))))

def VectorCheckedForward (sa : ScaleAlgebra F) (dim : Nat) (L : List F) : ZigResult (List F) :=
  match checkDim dim with
  | ZigResult.err e => ZigResult.err e
  | ZigResult.ok _ =>
    match checkLen dim L.length with
    | ZigResult.err e => ZigResult.err e
    | ZigResult.ok _ => ZigResult.ok (forwardVectorizedCore sa dim L)

def VectorCheckedBackward (sa : ScaleAlgebra F) (dim : Nat) (L : List F) : ZigResult (List F) :=
  match checkDim dim with
  | ZigResult.err e => ZigResult.err e
  | ZigResult.ok _ =>
    match checkLen dim L.length with
    | ZigResult.err e => ZigResult.err e
    | ZigResult.ok _ => ZigResult.ok (backwardVectorizedCore sa dim L)

theorem vector_checked_forward_refines_public (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h : L.length = dim + dim) :
  VectorCheckedForward sa dim L = forwardChecked sa dim L :=
  match dim with
  | 0 => Eq.refl _
  | Nat.succ k =>
    match Nat.decLt usizeHalf (Nat.succ k) with
    | Decidable.isTrue _ => Eq.refl _
    | Decidable.isFalse hn =>
      let h0 : Not (Nat.succ k = 0) := succ_not_zero k
      let hcf := checkLen_ok (Nat.succ k) L.length h
      let hvec := forwardVectorizedCore_eq_core sa (Nat.succ k) L h
      match hcf, hvec with
      | Eq.refl _, Eq.refl _ => Eq.refl _

theorem vector_checked_backward_refines_public (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h : L.length = dim + dim) :
  VectorCheckedBackward sa dim L = backwardChecked sa dim L :=
  match dim with
  | 0 => Eq.refl _
  | Nat.succ k =>
    match Nat.decLt usizeHalf (Nat.succ k) with
    | Decidable.isTrue _ => Eq.refl _
    | Decidable.isFalse hn =>
      let h0 : Not (Nat.succ k = 0) := succ_not_zero k
      let hcb := checkLen_ok (Nat.succ k) L.length h
      let hvec := backwardVectorizedCore_eq_core sa (Nat.succ k) L h
      match hcb, hvec with
      | Eq.refl _, Eq.refl _ => Eq.refl _

theorem vector_checked_forward_success (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h0 : Not (dim = 0)) (hno : Not (usizeHalf < dim)) (hlen : L.length = dim + dim) :
  VectorCheckedForward sa dim L = ZigResult.ok (forwardVectorizedCore sa dim L) :=
  let hp := vector_checked_forward_refines_public sa dim L hlen
  let hs := forward_checked_success sa dim L h0 hno hlen
  let hv := Eq.symm (forwardVectorizedCore_eq_core sa dim L hlen)
  let hok : ZigResult.ok (forwardCore sa dim L) = ZigResult.ok (forwardVectorizedCore sa dim L) := congrArg ZigResult.ok hv
  Eq.trans hp (Eq.trans hs hok)

theorem vector_checked_backward_success (sa : ScaleAlgebra F) (dim : Nat) (L : List F)
  (h0 : Not (dim = 0)) (hno : Not (usizeHalf < dim)) (hlen : L.length = dim + dim) :
  VectorCheckedBackward sa dim L = ZigResult.ok (backwardVectorizedCore sa dim L) :=
  let hp := vector_checked_backward_refines_public sa dim L hlen
  let hs := backward_checked_success sa dim L h0 hno hlen
  let hv := Eq.symm (backwardVectorizedCore_eq_core sa dim L hlen)
  let hok : ZigResult.ok (backwardCore sa dim L) = ZigResult.ok (backwardVectorizedCore sa dim L) := congrArg ZigResult.ok hv
  Eq.trans hp (Eq.trans hs hok)

theorem vector_checked_roundtrip_forward_backward (sa : ScaleAlgebra F) (dim : Nat) (L M : List F)
  (h0 : Not (dim = 0)) (hno : Not (usizeHalf < dim)) (hlen : L.length = dim + dim)
  (hf : VectorCheckedForward sa dim L = ZigResult.ok M) :
  VectorCheckedBackward sa dim M = ZigResult.ok L :=
  let hs := vector_checked_forward_success sa dim L h0 hno hlen
  match Eq.trans (Eq.symm hs) hf with
  | Eq.refl _ =>
    let hmlen0 := length_forwardCore sa dim L hlen
    let hvec_to_core := forwardVectorizedCore_eq_core sa dim L hlen
    let hmlen : (forwardVectorizedCore sa dim L).length = dim + dim :=
      match hvec_to_core with
      | Eq.refl _ => hmlen0
    let hb := vector_checked_backward_success sa dim (forwardVectorizedCore sa dim L) h0 hno hmlen
    let inv := forwardVectorizedCore_round_trip sa dim L hlen
    match hb, inv with
    | Eq.refl _, Eq.refl _ => Eq.refl _

theorem vector_checked_roundtrip_backward_forward (sa : ScaleAlgebra F) (dim : Nat) (L M : List F)
  (h0 : Not (dim = 0)) (hno : Not (usizeHalf < dim)) (hlen : L.length = dim + dim)
  (hb : VectorCheckedBackward sa dim L = ZigResult.ok M) :
  VectorCheckedForward sa dim M = ZigResult.ok L :=
  let hs := vector_checked_backward_success sa dim L h0 hno hlen
  match Eq.trans (Eq.symm hs) hb with
  | Eq.refl _ =>
    let hmlen0 := length_backwardCore sa dim L hlen
    let hvec_to_core := backwardVectorizedCore_eq_core sa dim L hlen
    let hmlen : (backwardVectorizedCore sa dim L).length = dim + dim :=
      match hvec_to_core with
      | Eq.refl _ => hmlen0
    let hf := vector_checked_forward_success sa dim (backwardVectorizedCore sa dim L) h0 hno hmlen
    let inv := backwardVectorizedCore_round_trip sa dim L hlen
    match hf, inv with
    | Eq.refl _, Eq.refl _ => Eq.refl _

theorem tensor_forward_backward_roundtrip_after_init (sa : ScaleAlgebra F) (dim : Nat) (hd : ValidDim dim) (x : TensorMem F)
  (hlen : x.data.length = dim + dim) :
  match forwardInPlaceChecked sa (oftbInitSpec dim hd) x with
  | ZigResult.err _ => False
  | ZigResult.ok y => backwardInPlaceChecked sa (oftbInitSpec dim hd) y.data = ZigResult.ok x.data ∧ y.shape = x.shape :=
  let hf := init_forward_public_post sa dim hd x hlen
  match hf with
  | Eq.refl _ =>
    let h0 := valid_dim_not_zero dim hd
    let hno := valid_dim_no_overflow_lt dim hd
    let hlen2 := length_forwardCore sa dim x.data hlen
    let hb := backward_checked_success sa dim (forwardCore sa dim x.data) h0 hno hlen2
    let inv := oftb_invertible sa dim x.data hlen
    match hb, inv with
    | Eq.refl _, Eq.refl _ => And.intro (Eq.refl _) (Eq.refl _)

theorem tensor_backward_forward_roundtrip_after_init (sa : ScaleAlgebra F) (dim : Nat) (hd : ValidDim dim) (x : TensorMem F)
  (hlen : x.data.length = dim + dim) :
  match backwardInPlaceChecked sa (oftbInitSpec dim hd) x.data with
  | ZigResult.err _ => False
  | ZigResult.ok y => forwardInPlaceChecked sa (oftbInitSpec dim hd) (tensorSetData x y) = ZigResult.ok x :=
  let hb := init_backward_public_post sa dim hd x.data hlen
  match hb with
  | Eq.refl _ =>
    let h0 := valid_dim_not_zero dim hd
    let hno := valid_dim_no_overflow_lt dim hd
    let hlen2 := length_backwardCore sa dim x.data hlen
    let hf := forward_in_place_success sa (oftbInitSpec dim hd) (tensorSetData x (backwardCore sa dim x.data)) h0 hno hlen2
    let inv := oftb_invertible_rev sa dim x.data hlen
    match hf, inv with
    | Eq.refl _, Eq.refl _ => Eq.refl _

end ZigOFTBDeepArchitecture
