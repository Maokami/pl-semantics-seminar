# PL 스터디 교재 이용 안내

매주 모두 같은 장을 읽고, 돌아가며 한 사람이 그 장을 발표합니다. 교재는 영어로 읽고 질문과 토론은 한국어로 해도 됩니다. [교재 목차](https://maokami.github.io/pl-semantics-seminar/)

## 모임 전 · 이번 장 읽기

도입 문단 뒤의 **In this session**에서 이번 장의 대표 정리와 칠판에서 다룰 경우를 확인하세요. 본문을 읽다가 증명의 한 단계가 걸리면 그 문장을 선택하세요. 수식을 선택하기 어려우면 장 끝의 **Choose a passage**를 누르고 문단을 고를 수 있습니다.

| 하고 싶은 일 | 교재에서 하는 방법 |
|---|---|
| 동료에게 같은 문단 보여 주기 | **Copy passage link**를 눌러 팀 채팅에 붙입니다. 링크를 열면 해당 문단이 강조됩니다. |
| 짧은 질문, 다른 풀이, 예제 나누기 | 장 끝 **Chapter discussion**에서 댓글을 쓰거나 기존 댓글에 답합니다. 문장을 인용하려면 본문에서 **Copy quote for chapter discussion**을 누른 뒤 댓글란에 붙여 넣으세요. |
| 답을 따로 추적할 질문 남기기 | 문장을 선택하고 **Ask a question**을 누릅니다. GitHub에서 인용문과 링크를 확인하고 새 Q&A를 게시하세요. 기존 질문은 **Questions from readers**에서 제목을 누르면 교재 안에서 읽고 답할 수 있습니다. |
| 오타, 수식 오류, 설명 수정 제안하기 | **Suggest a correction**를 누르고 어떤 표현을 어떻게 바꾸면 좋을지 씁니다. 제안은 GitHub Issue로 게시되어 처리 과정을 볼 수 있습니다. |

예를 들어 1장을 읽다가 “변수 이름이 무한히 많은데 상태가 모든 변수의 값을 준다는 건 무슨 뜻인가요?”라는 의문이 들면, 정의 1.2의 첫 문장을 선택한 뒤 질문을 남겨 주세요. 읽는 사람도 같은 정의에서 출발할 수 있습니다. [정의 1.2 · States](https://maokami.github.io/pl-semantics-seminar/chapter-01/#ch01-s1-p-definition-1-2)

질문이나 수정 제안에 본문의 수식을 다시 쓰려면 **Insert a formula → From this passage**에서 수식을 고르세요. **Common notation**에서는 평가 판단, 상태 갱신, 타입 판단 등의 예를 넣어 기호만 수정할 수 있습니다. 직접 입력한 `$…$` 또는 `$$…$$`도 **Math preview**에서 확인한 뒤 게시할 수 있습니다.

GitHub에서 곧바로 질문이나 정정을 만들 때는 본문에 장 번호를 한 줄로 적으세요(예: `Session: 01`). 제목을 바꿔도 교재가 같은 장에서 글을 찾습니다.

댓글과 답글은 교재와 GitHub Discussions에서 함께 보이는 공개 글입니다. 읽기는 로그인 없이 가능하고, 교재에서 처음 글을 쓸 때는 **Sign in with GitHub**를 눌러 댓글 도구인 giscus를 승인합니다. 댓글창을 불러올 수 없는 환경에서는 **View on GitHub**를 이용하세요. [1장 토론 바로가기](https://maokami.github.io/pl-semantics-seminar/chapter-01/#chapter-discussion)

GitHub에서 질문을 올리거나 삭제한 뒤 교재 탭으로 돌아오면 **Questions from readers** 목록을 다시 불러옵니다. 같은 화면에 머무는 동안 다른 사람이 바꾼 내용은 목록 옆의 **Refresh**로 확인하세요.

## 직접 해 보기

각 장의 **Exercises**에는 번호가 붙은 연습문제가 먼저 나오고, 그 아래에 **Reconstruct the proof**가 있습니다. 이를 펼쳐 이번 장의 칠판 문제를 직접 풀어 보세요. 4–38장에서는 **Show proof outline**을 눌러 원고의 증명 개요와 대조할 수 있습니다. 나머지 연습문제도 먼저 풀어 보고 **Solutions and Further Reading**에서 풀이를 대조하세요. 1–3회에는 **Exercises → Open Lean editor**가 있습니다. 1회에서는 상태에서 변수 x의 값이 3일 때 x + 4가 7로 평가된다는 증명을 완성합니다. 편집기에서 `plusFour`를 찾아 `sorry`를 증명으로 바꿔 보세요. 작성한 코드는 편집기의 다운로드 기능으로 보관할 수 있습니다. 여러 파일을 함께 보려면 **Open project workspace**에서 실습 저장소 전체를 열 수 있습니다. [Lean 실습 저장소](https://github.com/Maokami/pl-semantics-labs)

## 발표를 맡은 주

**Reading for the Seminar**에서 원전의 지정 대목을 확인하고, 대표 정리의 가정과 결론, 증명에서 가장 설명하고 싶은 단계 하나를 준비하세요. **Chapter discussion**과 **Questions from readers**를 함께 살펴보면 스터디원들이 어떤 대목에서 막혔는지 알 수 있습니다. 모임에서 해결한 질문은 해당 글에 답글로 남겨 다음에 읽는 사람도 찾아볼 수 있게 해 주세요.

## 의견 처리 상태 확인

각 장의 **Corrections and review**에서 최근 수정 요청과 **Chapter review decisions**를 확인하세요. 일반 질문은 토론에서 답합니다. 교재 수정이 필요하면 해당 댓글 링크를 정정 요청에 넣어 주세요. 수동 검토와 자동 검토는 같은 정정 기록을 사용합니다. 짧은 간격의 변경은 모아서 처리하고, 승인 대기 중인 변경안이 있으면 그 결정 뒤에 다음 의견을 검토합니다. 매일 09:37에도 누락된 의견을 확인합니다. 관리자가 승인해야 교재에 반영되며, 원래 Issue나 Discussion에 제안·승인·거부·게시 상태를 연결한 댓글이 갱신됩니다. 거부 사유는 연결된 PR의 댓글에서 확인할 수 있습니다.
