#import "style.typ": *
#show: document-layout.with("PL 스터디 · 회차표")

= 프로그래밍 언어 이론
정규 32회와 조건부 6회. 회차별 주제와 대표 정리는 강의계획서 4절을 따른다.

#let schedule = read("docs/curriculum.ko.md").split("## 4. 회차표").at(1).split("### 정규에서").first()
#for line in schedule.split("\n") {
  if line.starts-with("### ") {
    heading(level: 2, line.slice(4))
  } else if line.starts-with("| ") {
    let cells = line.trim("|").split("|").map(c => c.trim())
    if cells.first() != "회" {
      block(breakable: false)[
        *#(cells.at(0))회 · #(cells.at(1))* \
        #(cells.at(2)) #small(cells.at(3))
      ]
    }
  } else if line.starts-with("T는 ") {
    par(line)
  }
}
