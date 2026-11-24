import PLBook.Korean

open Verso Verso.Genre Verso.Genre.Manual Verso.Output.Html

-- The translation uses the same chapter and theorem numbers as the English edition.
private def prefixTitle (p : Doc.Part Manual) (lead : String) : Doc.Part Manual :=
  { p with
    title := #[.text (lead ++ p.titleString)]
    titleString := lead ++ p.titleString
    metadata := some { p.metadata.getD {} with number := false } }

private def courseChapter (p : Doc.Part Manual) : Doc.Part Manual := Id.run do
  let tag := (p.metadata.getD {}).tag.getD ""
  let n := ((tag.drop 2).toString.toNat?).getD 0
  let mut i := 0
  let mut numbered := #[]
  for s in p.subParts do
    if (s.metadata.getD {}).number then
      i := i + 1
      numbered := numbered.push (prefixTitle s s!"{n}.{i}. ")
    else
      numbered := numbered.push s
  return { prefixTitle p s!"{n}. " with subParts := numbered }

def main := manualMain
  (let book := %doc PLBook.Korean
   { book with subParts := book.subParts.map courseChapter })
  (config := {
    htmlDepth := 1
    emitHtmlMulti := .immediately
    extraHead := #[
      {{<link rel="stylesheet" href="static/reader.css"/>}},
      {{<script defer="defer" src="static/reader.js"></script>}}]
  })
