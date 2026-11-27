# 독자 의견에서 교재 개정까지

공개 교재의 댓글은 GitHub Discussions와 같은 글입니다. 문단에서 **Ask a question**은 Q&A를, **Suggest edit / Suggest a correction**은 `textbook feedback` Issue를 만듭니다. 원문 인용, 장·절 링크와 원고 리비전이 함께 전달됩니다. 별도로 양쪽에 중복 게시할 필요가 없습니다.

## 자동 검토

- **Continuous reader feedback**: 매일 00:37 UTC (09:37 KST), 또는 Actions의 **Run workflow**로 실행합니다. 실제 시작은 GitHub 스케줄 사정에 따라 늦어질 수 있습니다.
- 열린 수정 Issue와 장별 Discussion 본문·댓글·답글을 끝까지 읽습니다. 빈 장별 토론과 봇 알림은 건너뜁니다. 원문 또는 사람의 댓글이 바뀌면 다시 검토합니다.
- 한 번에 최대 세 건을 한 PR로 준비하며, 승인 대기 중인 AI 제안이 있으면 다음 제안은 기다립니다. 승인/거부한 동일 내용은 반복 제출하지 않습니다.
- AI는 커리큘럼, 현재 장과 해설을 대조합니다. 원고를 바꾸는 제안뿐 아니라 이미 반영됨/추가 토론 필요 판단도 근거와 함께 `feedback/reviews/`에 기록합니다.
- AI의 쓰기 범위는 장 원고·용어집·언어 카드와 검토 기록입니다. 정의/증명 모듈, 워크플로, 비밀, 배포 설정은 바꿀 수 없고, 직접 merge할 권한을 주지 않습니다.
- 격리된 임시 작업 공간에서는 파일 검사·편집·로컬 Git 명령을 실행할 수 있습니다. 저장소에 쓰는 권한은 별도 `safe_outputs` 작업에만 있으며, 허용 경로·파일 수·패치 크기를 검사한 PR 생성으로 제한합니다. AI의 GitHub 조회 도구는 읽기 전용입니다.
- 기존 **Seminar reading brief**는 목요일 09:13 KST 발표용 요약을 계속 담당합니다. **Reader correction review**는 수동 답변 초안 도구이며 교재 수정 파이프라인과 별개입니다.

## 관리자의 승인·거부

[검토 대기 목록](https://github.com/Maokami/pl-semantics-seminar/pulls?q=is%3Apr+is%3Aopen+label%3A%22reader+proposal%22)을 엽니다. 각 장 **Corrections and review → How review works → Maintainer review queue**에서도 갈 수 있습니다.

1. PR의 원래 의견 링크, 판단 근거, **Files changed**를 확인합니다.
2. **Reader feedback / book** 검사가 초록색인지 확인합니다. 전체 Lean/Verso 빌드와 학습 링크를 검사하며, Actions artifact `reader-preview-N`에 생성 HTML을 제공합니다. 실패하면 merge하지 말고 수정 요청을 남깁니다.
3. **승인:** **Merge pull request** (또는 Squash and merge) 후 확인 버튼을 누릅니다. PR의 **Approve** 리뷰만으로는 게시되지 않습니다. 관리자가 merge해야 GitHub Pages 빌드·게시가 시작됩니다.
4. **거부:** PR 댓글에 이유를 쓰고 **Comment and close pull request**를 누릅니다. 사유 없이 Close만 해도 거부되지만 이유를 권장합니다. 원래 Issue/Discussion에는 결정 기록 링크가 갱신됩니다. 원래 독자의 글은 자동으로 닫거나 삭제하지 않습니다.
5. **다시 논의:** 거부한 PR을 Reopen하거나 원래 의견에 새로운 설명을 추가합니다. 새로운 사람의 댓글/본문 변경은 다음 자동 검토 대상입니다.

제안 생성, 승인, 거부, GitHub Pages 게시 완료를 구분해 원래 글의 봇 댓글 하나를 갱신합니다. 승인만으로 게시 완료라고 표시하지 않습니다. **Chapter review decisions**에는 거부/승인한 PR도 남습니다.

GitHub Actions의 기본 토큰으로 만든 PR은 일반 `pull_request` CI를 자동 실행하지 않습니다. 따라서 **Reader feedback checks and decisions**가 AI 실행 완료 뒤 검사하며, 사람의 PR 업데이트에도 다시 검사합니다. PR 코드는 읽기 전용 빌드 작업에서만 실행하고, 알림/검사 상태 쓰기는 신뢰된 기본 브랜치의 별도 작업에서 수행합니다.

## 운영과 확인

필수 기존 Secret: `ANTHROPIC_API_KEY`. PR 생성은 저장소의 **Actions → General → Workflow permissions → Allow GitHub Actions to create and approve pull requests** 설정이 허용해야 합니다. 개인 토큰을 원고나 사이트에 넣지 않습니다.

AI 실행 상한은 20분, 35턴, 주 세션 USD 2입니다. gh-aw의 별도 위협 검사 비용과 GitHub Actions 사용량까지 포함한 총비용 상한은 아닙니다. 의견이 없거나 검토 대기 PR이 있으면 AI를 호출하지 않습니다. 워크플로 파일을 변경할 때는 `gh aw` v1.2.2로 다시 컴파일합니다.

정상 운영 확인은 **Continuous reader feedback → Run workflow → smoke_test=true**로 할 수 있습니다. 교재 대신 검사용 JSON 하나만 담은 `[Smoke test]` PR을 만듭니다. `Reader feedback / book` 성공을 확인하고 **merge하지 말고 Close**합니다. 이 검사는 실제 독자 글에 알림을 쓰지 않습니다.

PR 생성 권한이 없으면 gh-aw 1.2.2는 `fallback-as-issue: false`에도 대체 Issue를 만들고 실행을 초록색으로 끝낼 수 있습니다. 따라서 후속 검사는 이를 실패로 표시하고, 열린 대체 Issue가 있는 동안 일반 AI 검토를 멈춰 중복 비용과 알림을 방지합니다. 위 권한 설정을 켠 뒤 `smoke_test=true`로 재검증하고 기존 대체 Issue를 닫아야 일반 검토가 재개됩니다. 시험용 제안은 병합하지 않습니다.

실패한 AI 실행은 성공한 검토로 처리하지 않으므로 다음 실행에서 재시도합니다. 빌드가 실패한 PR은 검사 로그를 보고 수정합니다. API 실패는 빈 의견 목록으로 숨기지 않고 실패로 표시합니다. 기존 원고 수정 검토의 초록색 결과만 보고 AI가 실행됐다고 판단하지 말고 `agent` 작업이 실제 실행됐는지 확인합니다.

자동 검사 통과는 수학적·교육적 타당성의 최종 승인이 아닙니다. 그 판단은 관리자가 PR에서 합니다.

## 교재 게시 위치

운영 교재는 [GitHub Pages](https://maokami.github.io/pl-semantics-seminar/)입니다. 관리자가 승인한 변경의 빌드가 성공하면 자동 게시됩니다.

관리자의 요청에 따라 **승인된 PL 교재 Sites 동기화** 예약은 비활성화했습니다. 기존 ChatGPT Site와 소스는 그대로 보존하며, 이후 교재 개정은 GitHub Pages에만 게시합니다.
