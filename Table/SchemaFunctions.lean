import Table.Schema

universe u_η
universe u

variable {η : Type u_η} [dec_η : DecidableEq η] {schema : @Schema η}

/- # Reducible Reimplementations of List Functions -/
-- This is just `List.append`, but we need it to be reducible, and Lean 4
-- doesn't allow us to modify the reducibility attribute of that function from
-- outside the `List` module
@[reducible]
def Schema.append {α} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys

theorem Schema.append_eq_List_append :
  ∀ (s s' : List α), Schema.append s s' = List.append s s'
  | [], _ => rfl
  | h :: hs, hs' => congrArg (h :: ·) $ append_eq_List_append hs hs'

@[reducible]
def Schema.map {α β} : (α → β) → List α → List β
  | _, [] => []
  | f, x :: xs => f x :: map f xs

@[simp]
theorem Schema.map_eq_List_map : @Schema.map = @List.map := by
  funext _ _ _ xs
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    simp only [map, List.map]
    exact congrArg _ ih

@[reducible]
def Schema.length {α} : List α → Nat
  | [] => 0
  | _ :: xs => length xs + 1

theorem Schema.length_eq_List_length : @Schema.length = @List.length := by
  funext _ xs
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    simp only [length, List.length]
    exact congrArg _ ih

@[reducible]
def Schema.nth {α} : (xs : List α) → (n : Nat) →
                     (n < Schema.length xs) → α
| x :: xs, 0, h => x
| x :: xs, Nat.succ n, h => nth xs n (Nat.le_of_succ_le_succ h)

-- TODO: eventually, we need to reconcile `nth` and `get`, but for now...
theorem Schema.nth_eq_get :
  ∀ (xs : List α) (n : Nat) (hn : n < Schema.length xs),
  Schema.nth xs n hn = xs.get ⟨n, Schema.length_eq_List_length ▸ hn⟩
| x :: xs, 0, h => rfl
| x :: xs, Nat.succ n, h => nth_eq_get xs n (Nat.le_of_succ_le_succ h)

-- TODO: need `map` to be reducible as well -- don't really want to reimplement
-- everything from scratch
@[reducible]
def Schema.nths {α} (xs : List α) (ns : List (Fin $ Schema.length xs))
  : List α :=
  Schema.map (λ n => Schema.nth xs n.1 n.2) ns

theorem Schema.length_nths (xs : List α) (ns : List (Fin $ Schema.length xs)) :
  List.length (Schema.nths xs ns) = List.length ns := by
  rw [nths, Schema.map_eq_List_map]
  apply List.length_map

@[reducible]
def Schema.sieve {α} : List Bool → List α → List α
| [], xs => xs
| _, [] => []
| true :: bs, x :: xs => x :: sieve bs xs
| false :: bs, _ :: xs => sieve bs xs

theorem Schema.sieve_eq_List_sieve : @Schema.sieve = @List.sieve :=
funext λ τ => funext λ bs => funext λ xs =>
  let rec pf : ∀ bs xs, sieve bs xs = List.sieve bs xs := λ
    | [], xs => by simp only [sieve, List.sieve]
    | _ :: _, [] => by simp only [sieve, List.sieve]
    | true :: bs, x :: xs => congrArg (x :: ·) (pf bs xs)
    | false :: bs, _ :: xs => pf bs xs
  pf bs xs

/- -------------------- -/

theorem List.length_rw {T : α → Type _} {s t : α} :
  ∀ (xs : List (T s)) (h : s = t), xs.length = (h ▸ xs).length
  | _, .refl _ => rfl


-- Lemmas for selectColumns2_spec2
theorem Schema.get_nths_eq_get_get :
  ∀ (xs : List α) (ns : List (Fin $ Schema.length xs))
  (i : Nat) (hi : i < List.length ns),
  List.get (Schema.nths xs ns) ⟨i, length_nths xs ns ▸ hi⟩ =
  List.get xs (List.get (Schema.length_eq_List_length ▸ ns)
    ⟨i, List.length_rw (T := λ f => Fin (f xs)) ns Schema.length_eq_List_length
        ▸ hi⟩)
| xs, n :: ns, 0, hi => by
  simp only [nths, map, get]
  rw [nth_eq_get]
  simp only [List.get]
  sorry
| xs, n :: ns, .succ i, hi => by
  simp only [nths, map]
  rw [nth_eq_get]
  simp only [List.get]
  have ih := get_nths_eq_get_get xs ns i (Nat.le_of_succ_le_succ hi)
  sorry
  -- simp only [←nths._eq_1]
  -- rw [←ih]

theorem List.get_map :
  ∀ (f : α → β) (xs : List α) (i : Fin xs.length),
  f (get xs i) = get (map f xs) ⟨i.val, (length_map xs f).symm.subst i.isLt⟩
| f, x :: xs, ⟨0, hi⟩ => rfl
| f, x :: xs, ⟨.succ i, hi⟩ => get_map f xs ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem Schema.get_map_nths_eq_get_get :
  ∀ (xs : List (α × β)) (ns : List (Fin $ Schema.length xs)) (i : Nat)
    (hi : i < ns.length),
  (List.map Prod.fst (nths xs ns)).get ⟨i,
    List.length_map (nths xs ns) Prod.fst ▸ length_nths xs ns ▸ hi
  ⟩ =
  (List.map Prod.fst xs).get ⟨(ns.get ⟨i, hi⟩).val,
    -- (List.length_map xs Prod.fst).symm ▸ (List.get ns ⟨i, hi⟩).isLt
    sorry
  ⟩
| xs, n :: ns, 0, hi => by
  simp only [nths, map, get]
  sorry
  -- rw [nth_eq_get]
  -- simp only [List.get]
  -- rw [List.get_map Prod.fst]
| xs, n :: ns, .succ i, hi => by
  simp only [nths, map, get]
  have ih := get_map_nths_eq_get_get xs ns i (Nat.lt_of_succ_lt_succ hi)
  simp only [List.get]
  rw [←ih]


@[reducible]
def Schema.hasAppendedHead :
  ∀ (sch : @Schema η) (c : η) (τ : Type _) (hs : List Header),
  HasCol (c, τ) (Schema.append sch ((c, τ) :: hs))
| [], _, _, _ => .hd
| s :: ss, c, τ, _ => .tl (hasAppendedHead ss c τ _)

def Schema.hasNameOfAppend : {sch : @Schema η} →
                                 {nm : η} →
                                 {hs : @Schema η} →
                                 sch.HasName nm →
  -- Schema.HasName nm (Schema.append sch hs)
  Schema.HasName nm (Schema.append sch hs)
| _, _, _, Schema.HasName.hd => Schema.HasName.hd
| _, _, _, Schema.HasName.tl h => Schema.HasName.tl $ hasNameOfAppend h

def Schema.hasColOfAppend : {sch : @Schema η} →
                                 {nm : η} →
                                 {τ : Type u} →
                                 {hs : List Header} →
                                 sch.HasCol (nm, τ) →
  Schema.HasCol (nm, τ) (Schema.append sch hs)
| _, _, _, _, Schema.HasCol.hd => Schema.HasCol.hd
| _, _, _, _, Schema.HasCol.tl h => Schema.HasCol.tl $ hasColOfAppend h

def Schema.hasColOfPrepend : {sch : @Schema η} →
                                 {nm : η} →
                                 {τ : Type u} →
                                 {hs : @Schema η} →
                                 sch.HasCol (nm, τ) →
  Schema.HasCol (nm, τ) (Schema.append hs sch)
| _, _, _, [], pf => pf
| _, _, _, _ :: hs', pf => .tl $ hasColOfPrepend (hs := hs') pf

theorem Schema.lookup_eq_lookup_append :
  ∀ (s : @Schema η) (t : @Schema η) (c : η) (h : s.HasName c),
  lookup s ⟨c, h⟩ = lookup (Schema.append s t) ⟨c, Schema.hasNameOfAppend h⟩ :=
by intros s t c h
   induction h with
   | hd =>
     simp only [Schema.hasNameOfAppend]
     rw [Schema.lookup_eq_1, Schema.lookup_eq_1]
   | tl h' ih =>
     simp only [Schema.hasNameOfAppend]
     rw [Schema.lookup_eq_2, Schema.lookup_eq_2]
     exact ih

-- Used in `dropColumn_spec2` proof
theorem Schema.mem_map_of_HasName : ∀ (sch : @Schema η) (nm : η),
  Schema.HasName nm sch → nm ∈ Schema.map Prod.fst sch := by
  intro sch nm h
  induction h with
  | hd =>
    apply List.Mem.head
  | tl _ ih =>
    apply List.Mem.tail
    apply ih


/- Retype from subschema: `update` -/
@[reducible]
def Schema.retypedFromSubschema :
  ∀ {sch : @Schema η}, RetypedSubschema sch → @Schema η
| hs, [] => hs
| hs, ⟨(_, ρ), pf⟩ :: rs =>
  @retypedFromSubschema (hs.retypeColumn pf ρ)
    (Schema.map (λ ⟨h, pf⟩ => ⟨h, Schema.hasRetypedName pf⟩) rs)
termination_by retypedFromSubschema rs => rs.length

@[reducible]
def Schema.retypedSubschemaHasSchemaName :
  ∀ {sch : @Schema η} {nm : η} (rs : RetypedSubschema sch),
  HasName nm sch → HasName nm (Schema.retypedFromSubschema rs)
| sch, nm, [], hnm => hnm
| (_, _) :: _, nm, ⟨(_, _), _⟩ :: rs', pf =>
  retypedSubschemaHasSchemaName (Schema.map _ rs') (Schema.hasRetypedName pf)
termination_by retypedSubschemaHasSchemaName rs h => rs.length

@[reducible]
def Schema.retypedFromSubschemaHasNameOfRSToSchema :
  ∀ {sch : @Schema η} {rs : RetypedSubschema sch} {nm : η},
  HasName nm rs.toSchema → HasName nm (Schema.retypedFromSubschema rs)
| [], ⟨_, hrs⟩ :: _, _, _ => nomatch hrs
| (_, _) :: _, [_], _, .tl h => nomatch h
| sch, ⟨hdr, hnm⟩ :: rest, nmToFind, hntf =>
  have hsch := Schema.schemaHasRetypedSubschemaName hntf
  retypedSubschemaHasSchemaName _ hsch

theorem Schema.retypedFromSubschema_preserves_names :
  ∀ (sch : @Schema η) (rs : RetypedSubschema sch),
  Schema.names (Schema.retypedFromSubschema rs) = Schema.names sch
| ss, [] => rfl
| (_, _) :: ss, ⟨(nm, τ), pf⟩ :: rs =>
  by
    simp only [retypedFromSubschema]
    have := retypedFromSubschema_preserves_names (Schema.retypeColumn _ pf τ)
      (Schema.map (fun ⟨h, pf⟩ => ⟨h, hasRetypedName pf⟩) rs)
    rw [this]
    simp only [retypeColumn_preserves_names]
termination_by retypedFromSubschema_preserves_names sch rs => rs.length
