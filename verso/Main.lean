import PLBook

open Verso Verso.Genre Verso.Genre.Manual
open Verso.Output.Html

-- The earlier English chapter on program equivalence still declares the Session 6 URL.
-- Give that chapter its own address while it is included alongside the revised Session 6.
private def englishBook : Doc.Part Manual :=
  let book := %doc PLBook
  let old := %doc PLBook.Ch07
  { book with subParts := book.subParts.map fun part =>
      if part.titleString == old.titleString && (part.metadata.bind (·.file)) == some "chapter-06" then
        { part with
          metadata := part.metadata.map fun m => { m with file := "chapter-06-legacy", tag := "ch06-legacy" }
          subParts := part.subParts.map fun sec =>
            { sec with metadata := sec.metadata.map fun m =>
                { m with tag := m.tag.map (·.replace "ch06-" "ch06-legacy-") } } }
      else part }

def main := manualMain englishBook (config := {
  htmlDepth := 1
  emitHtmlMulti := .immediately
  extraFiles := [("static", "static")]
  extraHead := #[
    {{<link rel="stylesheet" href="static/reader.css"/>}},
    {{<script defer="defer" src="static/reader.js"></script>}}]
})
