import Table.API
import Table.Notation
import Table.Widgets
import Std.Internal.Parsec
import Lean

namespace Table

/--
A universe-polymorphic IO monad that does not use `unsafe` features.

This is a bare-bones implementation for demonstration purposes and is likely to be unpleasant to
work with in more complex use cases. This is adapted from Gabriel Ebner's proof-of-concept code:
https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.E2.9C.94.20Higher.20universes.20in.20.60IO.60
-/
abbrev PIO (α : Type u) := EStateM (ULift IO.Error) (ULift IO.RealWorld) α

namespace PIO

/-- Changes the universe of the result of a `PIO` computation. -/
def changeUniv {α : Type u} (k : PIO.{max u v} (ULift.{v} α)) : PIO.{max u w} (ULift.{w} α) :=
  fun ⟨w⟩ => match k ⟨w⟩ with
    | .ok ⟨x⟩ ⟨s⟩ => .ok ⟨x⟩ ⟨s⟩
    | .error ⟨e⟩ ⟨s⟩ => .error ⟨e⟩ ⟨s⟩

/-- Lifts a `PIO` resulting value in `Type` to the universe of the current `PIO` action. -/
def lift0 {α : Type} (k : PIO α) : PIO.{u} (ULift α) :=
  PIO.changeUniv (ULift.up <$> k)

/--
Converts a `PIO` action to an `IO` action.

The result must be discarded because we cannot guarantee its universe.
-/
def toIO {α : Type u} (k : PIO α) : IO Unit :=
  fun w => match k ⟨w⟩ with
    | .ok _ ⟨s⟩ => .ok () s
    | .error ⟨e⟩ ⟨s⟩ => .error e s

/-- Converts a `PIO` action that computes a value in `Type` to an `IO` action. -/
def toIO0 {α : Type} (k : PIO α) : IO α :=
  fun w => match k ⟨w⟩ with
    | .ok x ⟨s⟩ => .ok x s
    | .error ⟨e⟩ ⟨s⟩ => .error e s

instance : MonadLift IO PIO where
  monadLift k := fun ⟨w⟩ =>
    match k w with
    | .ok x s => .ok x ⟨s⟩
    | .error e s => .error ⟨e⟩ ⟨s⟩

def ofExcept [ToString ε] (e : Except ε α) : PIO α :=
  match e with
  | .ok a    => .ok a
  | .error e => .error ⟨IO.userError (toString e)⟩

end PIO

namespace CSV

open Std Internal
open Parsec (Input)
variable {η : Type u} [DecidableEq η]

open Parsec String

abbrev CSVCell := String
abbrev CSVRow := Array CSVCell

/-
Parsing logic is modified from Chris Lovett's (homogeneous) CSV parsing demo:
https://github.com/leanprover-community/lean4-samples/blob/main/CSVParser/CSVParser.lean
-/

def textData : Parser Char := satisfy fun c =>
  0x20 ≤ c.val ∧ c.val ≤ 0x21 ∨
  0x23 ≤ c.val ∧ c.val ≤ 0x2B ∨
  0x2D ≤ c.val ∧ c.val ≤ 0x7E

def cr : Parser Char := pchar '\r'
def lf : Parser Char := pchar '\n'
def crlf : Parser String := pstring "\r\n"
def comma : Parser Char := pchar ','
def dQuote : Parser Char := pchar '\"'
def twoDQuote  : Parser Char :=  attempt (pchar '"' *> pchar '"')

def escaped : Parser String := attempt
  dQuote *>
  manyChars (textData <|> comma <|> cr <|> lf <|> twoDQuote)
  <* dQuote

def nonEscaped : Parser String := manyChars textData

def cell : Parser String := escaped <|> nonEscaped

/-- Many `p` separated by `s`. -/
def manySep (p : Parser α) (s : Parser β) : Parser $ Array α := do
  manyCore (attempt (s *> p)) #[←p]

def row : Parser CSVRow := manySep cell comma

def file : Parser $ Array CSVRow :=
  manySep row (crlf <* notFollowedBy eof) <* (optional crlf) <* eof

inductive HeaderMode
  | checkHeader | skipHeader | noHeader

def parse (s : String) : Except String $ Array (Array String) :=
  match file s.mkIterator with
  | ParseResult.success _ res => Except.ok res
  | ParseResult.error it err  => Except.error s!"CSV parsing error at offset {it.i.byteIdx}: {err}"

class CSVParseable (τ : Type u) where
  parse : String → Option τ

instance : CSVParseable String where
  parse := some

instance : CSVParseable Nat where
  parse := String.toNat?

instance : CSVParseable Float where
  parse := fun s => Lean.JsonNumber.toFloat <$> (Parser.run Lean.Json.Parser.num s).toOption

class inductive ParseableSchema : @Schema η → Type _
  | nil : ParseableSchema []
  | cons [i : CSVParseable τ] : ParseableSchema hs → ParseableSchema ((nm, τ) :: hs)

instance parseableSchemaNil : ParseableSchema (η := η) [] := .nil

instance parseableSchemaCons {nm : η} [CSVParseable τ] : ParseableSchema hs → ParseableSchema ((nm, τ) :: hs) :=
  fun hhs => .cons hhs

macro "ps_inst" : tactic => `(tactic|
  repeat first | apply parseableSchemaNil | apply parseableSchemaCons | infer_instance
)

def isValidHeader [CSVParseable η] (sch : @Schema η) (csvRow : CSVRow) : Bool :=
  let schArr := sch.names.toArray
  let headerRow? := csvRow.mapM CSVParseable.parse
  match headerRow? with
  | none => false
  | some headerRow => schArr = headerRow

def rowOfCSVRow? {sch : @Schema η} (inst : ParseableSchema sch) (csvRow : CSVRow) : Except String (Row sch) :=
  go csvRow 0 inst
where
  go : {sch : @Schema η} → CSVRow → Nat → ParseableSchema sch → Except String (Row sch)
  | [], csvRow, i, _ =>
    if i = csvRow.size
    then .ok .nil
    else .error s!"too many columns (expected {i}, found {csvRow.size})"
  | _ :: hs, csvRow, i, .cons (i := _) ps =>
    if h : i < csvRow.size then
      go (sch := hs) csvRow (i + 1) ps |>.bind fun rest =>
        let raw := csvRow.get ⟨i, h⟩
        if raw = "" then
          .ok <| .cons .emp rest
        else
          match CSVParseable.parse raw with
          | none => .error s!"failed to parse column {i + 1} value `{raw}`"
          | some parsed => .ok <| .cons (.val parsed) rest
    else
      .error s!"not enough columns (expected {hs.length + 1}, found {csvRow.size})"

def parseCSV {η : Type u} [DecidableEq η] [CSVParseable η]
    (schema : @Schema η) (contents : String) (headerMode : HeaderMode := .checkHeader)
    (inst : ParseableSchema schema := by ps_inst) : Except String (Table schema) :=
  parse contents |>.bind fun csvRows =>
    match headerMode with
    | .noHeader => Table.mk <$> csvRows.toList.mapM (rowOfCSVRow? inst)
    | .skipHeader | .checkHeader =>
      if let some headerRow := csvRows[0]? then
        if headerMode matches .skipHeader || isValidHeader schema headerRow then
          Table.mk <$> (csvRows.extract 1 csvRows.size).toList.mapM (rowOfCSVRow? inst)
        else .error s!"invalid header row {headerRow}"
      else .error "missing header row"

def parseCSVFile {η : Type} [DecidableEq η] [CSVParseable η]
    (filePath : System.FilePath) (schema : @Schema η)
    (headerMode : HeaderMode := .checkHeader)
    (inst : ParseableSchema schema := by ps_inst) : PIO (Table schema) := do
  let ⟨contents⟩ ← PIO.lift0 do IO.FS.readFile filePath
  PIO.ofExcept <| parseCSV schema contents headerMode inst

end Table.CSV
