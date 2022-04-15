-- Variant on orElse that's useful for de-option-ifying cell values
def Option.orDefault {α} [Inhabited α] : Option α → α
| some x => x
| none => default

-- List utilities
inductive List.All {α} (p : α → Prop) : List α → Prop
| vac      : All p []
| sing {x} : p x → All p [x]
| cons {x xs} : p x → All p xs → All p (x::xs)

def List.prod {α β} (xs : List α) (ys : List β) : List (α × β) :=
  List.foldl List.append [] (List.map (λ x => List.map (λ y => (x, y)) ys) xs)

-- TODO: So List.nth *does* still exist in the prelude -- they just changed
-- the name to `List.get`...
def List.nth {α} : (xs : List α) → (n : Nat) → (n < List.length xs) → α
| [], _, h => absurd h (by intro nh; cases nh)
| x::xs, 0, h => x
| x::xs, Nat.succ n, h => nth xs n (Nat.le_of_succ_le_succ h)

def List.nths {α}
              (xs : List α)
              (ns : List {n : Nat // n < List.length xs}) : List α :=
  List.map (λ n => List.nth xs n.val n.property) ns

-- This is slick, but unfortunately, it breaks type inference
-- def List.sieve {α} (bs : List Bool) (xs : List α) : List α :=
--   List.zip bs xs |> List.filter Prod.fst
--                  |> List.map Prod.snd

def List.sieve {α} : List Bool → List α → List α
| [], xs => xs
| _, [] => []
| true :: bs, x :: xs => x :: sieve bs xs
| false :: bs, _ :: xs => sieve bs xs

-- TODO: Haven't actually done the big-O analysis, but it's probably more
-- efficient to make the recursive case x :: flatten (xs :: ys). Unfortunately,
-- the termination checker doesn't like that implementation.
-- Initial attempt was:
-- termination_by flatten xs => 
--   List.foldl (λ acc xs => acc + List.length xs + 1) 0 xs)
-- TODO: After all that, I don't think we even need this function after all...
def List.flatten {α} : List (List α) → List α
| [] => []
| [] :: ys => flatten ys
| (x :: xs) :: ys => (x :: xs) ++ flatten ys

def List.flatMap {α β} (f : α → List β) : List α → List β
| [] => []
| x :: xs => f x ++ flatMap f xs

-- TODO: I refuse to believe there isn't a simpler way to do this
def List.verifiedEnum : (xs : List α) → List ({n : Nat // n < xs.length} × α)
| [] => []
| z :: zs =>
  let xs := z :: zs;
  let rec vEnumFrom : (ys : {ys : List α // ys.length ≤ xs.length})
                      → {n : Nat // n < ys.val.length}
                      → List ({n : Nat // n < xs.length} × α)
                      → List ({n : Nat // n < xs.length} × α)
    | ⟨[], h⟩, n, acc => acc
    | ⟨y :: ys, hys⟩, ⟨0, hn⟩, acc => ((⟨0, @Nat.lt_of_lt_of_le 0 (length ys + 1) (length xs) (Nat.zero_lt_succ (length ys)) hys⟩, y) :: acc)
    | ⟨y :: ys, hys⟩, ⟨Nat.succ n, hn⟩, acc => vEnumFrom ⟨ys, @Nat.le_trans (length ys) (length ys + 1) (length xs) (Nat.le_succ (length ys)) hys⟩
                                        ⟨n, Nat.lt_of_succ_lt_succ hn⟩
                                        ((⟨Nat.succ n, Nat.lt_of_lt_of_le hn hys⟩, y) :: acc)
    vEnumFrom ⟨xs, Nat.le_refl (length xs)⟩ ⟨length xs - 1, by apply Nat.sub_succ_lt_self; apply Nat.zero_lt_succ⟩ []
termination_by vEnumFrom ys n acc => ys.val.length
-- | [] => []
-- | x :: xs => verifiedEnumFrom x :: xs ⟨length xs - 1, by
--   simp [length]
--   calc length xs - 1 ≤ length xs := by apply Nat.sub_le
--                    _ < length xs + 1 := by constructor
--   ⟩
