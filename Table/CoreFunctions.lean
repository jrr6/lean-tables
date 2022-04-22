import Table.CoreTypes
import Table.BuiltinExtensions

universe u_η
universe u

variable {η : Type u_η} [dec_η : DecidableEq η] {schema : @Schema η}

-- Cell accessor and conversion functions
def Cell.toOption {nm τ} : @Cell η dec_η nm τ → Option τ
| Cell.emp => Option.none
| Cell.val x => Option.some x

def Cell.name {nm τ} (_ : @Cell η dec_η nm τ) : η :=
  nm
def Cell.type {nm τ} (_ : @Cell η dec_η nm τ) := τ

def Subschema.toSchema {schm : @Schema η} (s : Subschema schm) : @Schema η := 
  s.map (λ x => x.val)

-- Schema proof generation/manipulation functions
def Schema.certify (schema : @Schema η) : List (CertifiedHeader schema) :=
  let rec certify_elts : (subschm : @Schema η) → List (CertifiedHeader subschm)
    | [] => []
    | (c, τ) :: hs =>
      let map_subproof :=
        λ (⟨hdr, h⟩ : CertifiedHeader hs) => ⟨hdr, Schema.HasCol.tl h⟩;
      ⟨(c, τ), Schema.HasCol.hd⟩ :: (certify_elts hs).map map_subproof;
  certify_elts schema

def Schema.colImpliesName {c : η} {τ : Type u} (p : schema.HasCol (c, τ))
    : schema.HasName c :=
by
  induction schema with
  | nil => contradiction
  | cons h hs ih =>
    cases p with
    | hd => apply HasName.hd
    | tl a => apply HasName.tl (ih a)

def Schema.certifyNames (schema : @Schema η) : List (CertifiedName schema) :=
  schema.certify.map (λ (⟨(c, _), h⟩ : CertifiedHeader schema) =>
                        ⟨c, colImpliesName h⟩)

-- Schema functions
def Schema.names {η : Type u_η} := List.map (@Prod.fst η (Type u))

-- TODO: when we come back to do uniqueness, this might be helpful
-- def Schema.removeName :
--     (s : @Schema η) → {c : η // s.HasName c} → @Schema η
/-
dite (c = nm)
       (λ _ => xs)
       (λ nh => (nm, τ) :: removeName xs ⟨c, by
        cases h with
        | hd => simp at nh
        | tl tl_h => apply tl_h
        ⟩)
-/
def Schema.removeName :
    (s : @Schema η) → η → @Schema η
| [], _ => []
| (nm, τ)::xs, c => if c = nm then xs else (nm, τ) :: removeName xs c

-- TODO: Uniqueness is evil...
def Schema.removeNames {η : Type u_η} [DecidableEq η] :
    (s : @Schema η) → List η → @Schema η
| ss, [] => ss
| ss, (y::ys) => removeNames (removeName ss y) ys

-- def Schema.lookup {η : Type u_η} [DecidableEq η]
--     : (s : @Schema η) → CertifiedName s → @Header η
-- | (nm, τ)::hs, ⟨c, hc⟩ =>
--   dite (nm = c)
--        (λ _ => (nm, τ))
--        (λ h => lookup hs ⟨c, match hc with | Schema.HasName.tl h' => h'⟩)

-- Returns the schema entry with the specified name
def Schema.lookup {η : Type u_η} [DecidableEq η]
    : (s : @Schema η) → CertifiedName s → @Header η
| (nm, τ)::_, ⟨_, Schema.HasName.hd⟩ => (nm, τ)
| (nm, τ)::hs, ⟨c, Schema.HasName.tl h'⟩ => lookup hs ⟨c, h'⟩

def Schema.pick {η : Type u_η} [DecidableEq η] (s : @Schema η)
    : List (CertifiedName s) → @Schema η
| [] => []
| c::cs => lookup s c :: pick s cs

-- Row utilities
def Row.singleCell {name τ} (x : τ) :=
  @Row.cons η dec_η name τ [] (Cell.val x) Row.nil

def Row.append {schema₁ schema₂} :
    @Row η _ schema₁ → Row schema₂ → Row (List.append schema₁ schema₂)
| Row.nil, rs₂ => rs₂
| Row.cons r₁ rs₁, rs₂ => Row.cons r₁ (append rs₁ rs₂)

def Row.map {schema} (f : ∀ n α, Cell n α → @Cell η dec_η n α)
    : Row schema → @Row η dec_η schema
| Row.nil => Row.nil
| @Row.cons _ _ n τ _ r₁ rs₁ => Row.cons (f n τ r₁) (map f rs₁)

def Row.foldr {β} {schema : @Schema η}
              (f : ∀ {nm α}, @Cell η dec_η nm α → β → β)
              (z  : β)
    : Row schema → β
| Row.nil => z
| Row.cons cell rs => f cell (foldr f z rs)

-- Not sure if we'll ever need this...
def Row.toList {schema : @Schema η} {α} (f : ∀ {n β}, @Cell η dec_η n β → α)
    : Row schema → List α
| Row.nil => []
| Row.cons c rs => f c :: toList f rs

-- TODO: probably makes more sense to move this to some general "collection"
-- interface rather than reimplementing for every type -- wonder if this is
-- something James is working on
-- It would also be nice if we could make this function less verbose.
-- Unfortunately, Lean's type-checker needs some help...
def Row.sieve {schema} :
    (bs : List Bool) → Row schema → @Row η dec_η (List.sieve bs schema)
| [], Row.nil => Row.nil
| [], Row.cons r rs => Row.cons r rs
| true :: bs, Row.nil => Row.nil
| false :: bs, Row.nil => Row.nil
| true :: bs, Row.cons r rs => Row.cons r (sieve bs rs)
| false :: bs, Row.cons r rs => sieve bs rs

def Row.nth {schema} : (rs : @Row η dec_η schema) →
                       (n : Nat) →
                       (h : n < List.length schema) →
                       let (nm, τ) := List.nth schema n h;
                       @Cell η dec_η nm τ
| Row.nil, _, h => absurd h (by intro nh; cases nh)
| Row.cons r rs, 0, h => r
| Row.cons r rs, Nat.succ n, h => nth rs n (Nat.le_of_succ_le_succ h)

-- It would be nice if Lean could figure out that we're structurally recursing,
-- but in the meantime, we have to provide a manual termination relation
def Row.nths {schema} :
    (ns : List {n : Nat // n < List.length schema})
      → Row schema
      → @Row η dec_η (List.nths schema ns)
| [], Row.nil => Row.nil
| [], Row.cons x xs => Row.nil
| n::ns, Row.nil => absurd n.property
                          (by intro nh; simp [List.length] at nh; contradiction)
| n::ns, r => Row.cons (Row.nth r n.val n.property) (nths ns r)
  termination_by nths ns r => List.length ns
