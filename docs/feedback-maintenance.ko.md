# 독자 의견에서 교재 개정까지

공개 교재의 댓글은 GitHub Discussions와 같은 글입니다. 문단에서 **Ask a question**은 Q&A를, **Suggest a correction**은 `textbook feedback` Issue를 만듭니다. 원문 인용, 장·절 링크와 원고 리비전이 함께 전달됩니다. 별도로 양쪽에 중복 게시할 필요가 없습니다.

## 자동 검토

- **Continuous reader feedback**는 아래 사건이 생기면 검토를 시작합니다. 매일 00:37 UTC (09:37 KST) 실행은 누락·실패 후 재확인을 위한 보조 수단으로 유지합니다. Actions의 **Run workflow**로 수동 실행할 수도 있습니다.
- 열린 `textbook feedback` Issue가 생성·재개되거나 제목·본문이 수정될 때, 해당 라벨이 붙을 때, 사람이 댓글을 작성·수정·삭제할 때 실행합니다. PR 댓글, 관련 없는 라벨, 닫힌 Issue와 봇 알림은 제외합니다.
- 관련 사건은 약 60초 기다린 뒤 최신 내용으로 수집합니다. 한 실행이 끝날 때까지 다음 실행은 대기하며, 연속 사건은 가장 최근 대기 실행으로 모입니다. 진행 중인 AI 검토는 새 댓글 때문에 취소하지 않습니다. GitHub 대기열에 따라 시작은 더 늦어질 수 있습니다.
- 한 번에 최대 세 건을 한 PR로 준비하며, 승인 대기 중인 AI 제안이 있으면 다음 제안은 기다립니다. 승인/거부한 동일 내용은 반복 제출하지 않습니다.
- 관리자가 AI 제안 PR을 Merge하거나 Close하면 결정 알림 작업이 끝난 뒤 대기 의견을 다시 확인합니다. 성공한 결정 작업의 저장소·원래 사건·닫힌 봇 PR을 확인하며, AI 실행 뒤의 일반 후속 검사나 게시 알림으로는 이 재검토를 시작하지 않습니다. 따라서 자동화끼리 서로를 반복 호출하지 않습니다.
- AI는 커리큘럼, 현재 장과 해설을 대조합니다. 원고를 바꾸는 제안뿐 아니라 이미 반영됨/추가 토론 필요 판단도 근거와 함께 `feedback/reviews/`에 기록합니다.
- AI의 쓰기 범위는 장 원고·용어집·언어 카드와 검토 기록입니다. 정의/증명 모듈, 워크플로, 비밀, 배포 설정은 바꿀 수 없고, 직접 merge할 권한을 주지 않습니다.
- 격리된 임시 작업 공간에서는 파일 검사·편집·로컬 Git 명령을 실행할 수 있습니다. 저장소에 쓰는 권한은 별도 `safe_outputs` 작업에만 있으며, 허용 경로·파일 수·패치 크기를 검사한 PR 생성으로 제한합니다. AI의 GitHub 조회 도구는 읽기 전용입니다.
- 기존 **Seminar reading brief**는 목요일 09:13 KST 발표용 요약을 계속 담당합니다. **Reader correction review**는 수동 답변 초안 도구이며 교재 수정 파이프라인과 별개입니다.

## 사람이 직접 고치는 경우

1. `python3 scripts/reader_feedback.py --queue`로 정정의 리비전 키와 원문 URL을 확인합니다. 일반 Q&A에는 답글을 남기고, 원고 수정이 필요하면 원래 댓글 영구 링크를 포함한 정정 Issue를 엽니다. 1장의 관리자 승인 원고는 원래 댓글과 대조한 파일에서 직접 검토합니다.
2. 원고와 함께 `feedback/reviews/<key>.json`을 제출합니다. 기존 1장 기록을 예로 삼아 `key`, `source_url`, `disposition`, `reason_ko`, `sections`, `validation`, `target`을 작성합니다. `target`은 해당 판에 존재하는 `chapter-NN/#문단ID`입니다. 독자가 공유한 이전 문단 ID를 새 문단으로 옮길 때는 `previous_anchors`에 추가합니다. 변경 종류는 `change`, 원고 유지 결정은 `no-change`, 추가 토론은 `needs-discussion`입니다.
3. PR에는 원문 링크와 실제 검사를 적고, 관리자가 `reader proposal` 라벨을 부여합니다. 같은 저장소의 권한 있는 기여자 PR은 검토 중부터 연결됩니다. 외부 fork의 검토 기록은 병합 뒤 연결됩니다. 독자는 원래 Issue 또는 Discussion에서 결정을 확인하고, 교재에서 개정된 문단을 열 수 있습니다.
4. 자동 검토가 대기 중이면 [한도와 복구 안내](review-recovery.ko.md)를 확인합니다. 병합된 기록은 다음 검토에서 같은 입력의 중복 제안을 막습니다.

## 관리자의 승인·거부

[검토 대기 목록](https://github.com/Maokami/pl-semantics-seminar/pulls?q=is%3Apr+is%3Aopen+label%3A%22reader+proposal%22)을 엽니다. 각 장 **Corrections and review → How review works → Maintainer review queue**에서도 갈 수 있습니다.

1. PR의 원래 의견 링크, 판단 근거, **Files changed**를 확인합니다.
2. **Textbook verification** 검사가 초록색인지 확인합니다. 전체 Lean/Verso 빌드와 학습 링크를 검사하며, Actions artifact `reader-preview-N`에 생성 HTML을 제공합니다. 실패하면 merge하지 말고 수정 요청을 남깁니다.
3. **승인:** **Merge pull request** (또는 Squash and merge) 후 확인 버튼을 누릅니다. PR의 **Approve** 리뷰만으로는 게시되지 않습니다. 관리자가 merge해야 GitHub Pages 빌드·게시가 시작됩니다.
4. **거부:** PR 댓글에 이유를 쓰고 **Comment and close pull request**를 누릅니다. 사유 없이 Close만 해도 거부되지만 이유를 권장합니다. 원래 Issue/Discussion에는 결정 기록 링크가 갱신됩니다. 원래 독자의 글은 자동으로 닫거나 삭제하지 않습니다.
5. **다시 논의:** 거부한 PR을 Reopen하거나 원래 의견에 새로운 설명을 추가합니다. 새로운 사람의 댓글/본문 변경은 다음 자동 검토 대상입니다.

제안 생성, 승인, 거부, GitHub Pages 게시 완료를 구분해 원래 글의 봇 댓글 하나를 갱신합니다. 승인만으로 게시 완료라고 표시하지 않습니다. **Chapter review decisions**에는 거부/승인한 PR도 남습니다.

원래 정정 Issue 전체가 해결되는 제안이면 관리자가 그 Issue에 `close after publication` 라벨을 붙일 수 있습니다. 승인한 PR의 커밋이 성공한 Pages 게시에 포함되고, 배포된 검토 기록이 모두 `change`일 때만 완료로 닫습니다. 기본값은 열린 상태 유지입니다. 거부·`no-change`·`needs-discussion` 결정, Discussion, 기록 없이 본문에서 언급만 된 Issue는 자동 종료하지 않습니다. 병합 뒤 Issue를 Reopen하면 같은 PR로 다시 닫지 않습니다. 아직 해결되지 않은 부분을 댓글로 남겨 새 검토를 요청하세요. 일반 GitHub `Closes #번호`는 게시 전에 병합 시점에 종료하므로 교재 수정 PR에는 사용하지 않습니다.

AI가 PR 본문의 연결 표식을 빠뜨린 경우에도, 변경된 `feedback/reviews/<key>.json`을 데이터로 읽어 원래 의견과 연결하고 중복 검토를 막습니다. 파일명과 키가 같은지, 출처가 이 저장소의 Issue/Discussion인지 검증하며 PR 코드를 실행하지 않습니다.

자동 생성 PR의 일반 `pull_request` CI는 자동 실행되지 않거나 별도의 실행 승인을 기다릴 수 있습니다. 따라서 **Reader feedback checks and decisions**가 AI 실행 완료 뒤 **Textbook verification**으로 해당 PR 커밋을 검사하며, 사람의 PR 업데이트에도 다시 검사합니다. CI 실행 승인은 교재 변경의 Merge 승인과 별개입니다. 다른 검사가 승인 대기 중이면 이름과 대상을 확인하고, 동일 변경에 대한 검증 없이 생략하지 마세요. PR 코드는 읽기 전용 빌드 작업에서만 실행하고, 알림/검사 상태 쓰기는 신뢰된 기본 브랜치의 별도 작업에서 수행합니다.

동일 커밋의 빌드가 실행 중이면 중복 빌드를 만들지 않습니다. 실패한 빌드는 새 독자 댓글만으로 반복 재시도하지 않습니다. 수정 커밋을 올리거나, **Reader feedback checks and decisions → Run workflow**로 재시도할 수 있습니다.

## 운영과 확인

관리자가 승인한 1장 검토 원고는 `feedback/submissions/chapter01-review.ko.md`에 보관합니다. **Publish approved Chapter 1 feedback → Run workflow**는 이 원고만 Discussion #1에 `github-actions[bot]` 명의로 게시하며, 관리자 요청 게시물임을 표시합니다. 같은 원고가 이미 있으면 중복 댓글을 만들지 않습니다. 게시 뒤 기존 **Continuous reader feedback**를 명시적으로 요청합니다. Actions 토큰으로 작성한 댓글은 일반 이벤트를 다시 발생시키지 않기 때문입니다.

의견 수집에서는 Discussion #1의 해당 봇 댓글이 기본 브랜치의 승인 원고와 정확히 일치하는 경우만 예외적으로 읽습니다. 다른 봇 알림, 표식만 복사한 글, 다른 토론에 올린 글은 이 예외에 포함하지 않습니다. 원고의 변경도 관리자 검토를 거쳐야 하며, AI 수정 제안 워크플로에는 이 경로의 쓰기를 허용하지 않습니다. 이 게시 경로는 ChatGPT GitHub 연결의 권한을 변경하거나 개인 토큰을 저장하지 않습니다.

Issue·PR의 해결 후보, 중복, 승인 대기와 운영 장애는 별도의 [정리 현황 #27](https://github.com/Maokami/pl-semantics-seminar/issues/27)에서 확인합니다. 이 자동화는 원고 수정이나 항목 종료를 수행하지 않습니다. [실행 조건과 관리자 결정 방법](maintenance-triage.ko.md)을 참고하세요.

필수 기존 Secret: `ANTHROPIC_API_KEY`. PR 생성은 저장소의 **Actions → General → Workflow permissions → Allow GitHub Actions to create and approve pull requests** 설정이 허용해야 합니다. 개인 토큰을 원고나 사이트에 넣지 않습니다.

AI 실행 상한은 20분, 35턴, 주 세션 USD 2입니다. gh-aw의 별도 위협 검사 비용과 GitHub Actions 사용량까지 포함한 총비용 상한은 아닙니다. 의견이 없거나 검토 대기 PR이 있으면 AI를 호출하지 않습니다. 워크플로 파일을 변경할 때는 `gh aw` v1.2.2로 다시 컴파일합니다.

정상 운영 확인은 **Continuous reader feedback → Run workflow → smoke_test=true**로 할 수 있습니다. 교재 대신 검사용 JSON 하나만 담은 `[Smoke test]` PR을 만듭니다. `Textbook verification` 성공을 확인하고 **merge하지 말고 Close**합니다. 이 검사는 실제 독자 글에 알림을 쓰지 않습니다.

PR 생성 권한이 없으면 gh-aw 1.2.2는 `fallback-as-issue: false`에도 대체 Issue를 만들고 실행을 초록색으로 끝낼 수 있습니다. 따라서 후속 검사는 이를 실패로 표시하고, 열린 대체 Issue가 있는 동안 일반 AI 검토를 멈춰 중복 비용과 알림을 방지합니다. 위 권한 설정을 켠 뒤 `smoke_test=true`로 재검증하고 기존 대체 Issue를 닫아야 일반 검토가 재개됩니다. 시험용 제안은 병합하지 않습니다.

실패한 AI 실행은 성공한 검토로 처리하지 않으므로 실패 대기 시간 뒤 재시도합니다. 빌드가 실패한 PR은 검사 로그를 보고 수정합니다. API 실패는 빈 의견 목록으로 숨기지 않고 실패로 표시합니다. 기존 원고 수정 검토의 초록색 결과만 보고 AI가 실행됐다고 판단하지 말고 `agent` 작업이 실제 실행됐는지 확인합니다.

자동 검사 통과는 수학적·교육적 타당성의 최종 승인이 아닙니다. 그 판단은 관리자가 PR에서 합니다.

## 교재 게시 위치

운영 교재는 [GitHub Pages](https://maokami.github.io/pl-semantics-seminar/)입니다. 관리자가 승인한 변경의 빌드가 성공하면 자동 게시됩니다.

관리자의 요청에 따라 **승인된 PL 교재 Sites 동기화** 예약은 비활성화했습니다. 기존 ChatGPT Site와 소스는 그대로 보존하며, 이후 교재 개정은 GitHub Pages에만 게시합니다.
