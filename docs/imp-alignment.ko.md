# IMP 정의 대조와 1–13회 반영 목록

[커리큘럼 v1.2 부록 B](curriculum.ko.md)를 집필에 적용할 때의 기준이다. [영어 정본의 언어 카드](../verso/PLBook/LanguageCard.lean) A.1–A.6을 공통 참조로 사용한다. 이름은 문자열, 상태는 이름 전체에서 수학적 정수로 가는 함수다. 같은 상태와 조건식에는 하나의 불 값이 정해진다.

## 원전 대조

리비전 `a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01`에 고정했다. [공유 모듈](../verso/PLBook/IMP/Language.lean)은 아래 정의를 같은 생성자와 인자 순서로 옮겼다. [시범 장의 증명](../verso/PLBook/IMP/Determinacy.lean)은 이 모듈을 가져온다.

| 카드 | 포트 위치 | 대조 결과 |
|---|---|---|
| A.1–A.3 | [Imp 13–35](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L13-L35), [148–149](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L148-L149) | 네 생성자, 정수 평가, 한 이름만 바꾸는 갱신. 함수는 상태를 먼저 받는다. 같은 식 문법에 대한 평가 판단은 교재 자체 정의다. |
| A.4 | [Imp 73–104](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L73-L104), [116–121](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L116-L121) | 조건식 생성자 여섯, 명령 생성자 다섯. ≤와 논리곱은 기본형이고 <와 논리합은 파생형이다. |
| A.5 | [Imp 172–188](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L172-L188) | 종료 실행 규칙 여섯. 조건문은 가드가 정한 명령의 유도 한 개를 받는다. 두 따름정리는 그 선택을 각 불 값에서 계산해 얻는다. |
| A.6 | [Imp 297–312](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L297-L312) · [Sequences 12–14](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Sequences.lean#L12-L14), [95–110](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Sequences.lean#L95-L110) | 한 걸음 규칙 여섯. 유한 경로는 길이 인자가 없는 귀납 관계다. 무한 경로는 자연수로 색인한 함수와 공귀납 술어가 모두 있다. |

## 장별 적용

| 현 장 | 집필 시 반영할 내용 |
|---|---|
| 1 | 이름의 범위를 문자열로 명시한다. 뺄셈을 구문·함수·평가 판단·일치 보조정리의 귀납에 추가한다. 함수와 판단의 대응을 자체 정리로 싣는다. 치환은 11회의 읽기로 둔다. |
| 2 | 상태 기호를 s, t, u로 맞추고 조건식의 값과 여섯 실행 규칙을 A.4–A.5로 통일한다. 참·거짓 분기 규칙은 따름정리로 제시한다. |
| 3 | 시범 장에 반영했다. 하나의 조건문 규칙을 역전하고 순차·반복의 두 중간 상태를 일치시킨다. |
| 4 | 공유 산술식의 네 생성자(문자열 이름, 정수, 덧셈, 뺄셈)에 대해 임의의 결과 집합으로 가는 접기의 존재와 유일성을 증명했다(정리 4.1). |
| 5 | A.6의 여섯 전이 규칙과 진행(5.3), 길이 있는 경로와 유한 경로의 대응(5.4), 자연수로 색인한 무한 경로의 구성(5.5)을 실었다. 공귀납 술어의 의미도 구분했다. |
| 6 | 경로 올리기(6.1)는 길이까지 보존한다. 두 의미론의 대응(6.2)은 같은 최종 저장소의 skip을 끝점으로 삼는다. 역방향은 5.4로 길이를 얻고 6.3으로 첫 전이를 복원한다. |
| 7 | 루프를 한 번 펼친 조건문의 두 가지 동작을 A.5에서 유도한다. 관찰 대상은 종료 시점의 상태 전체다. |
| 8 | 부분 상태 변환의 입력과 정상 결과를 A.2의 상태로 잡는다. 평탄 순서와 합성은 v1.2에 지정된 S2·Reynolds의 정의와 연결한다. |
| 9 | 반복 연산자의 가드를 A.4의 불 값으로 읽고, 뺄셈 예제는 A.1의 기본 생성자로 해석한다. |
| 10 | 관계 의미의 상태 쌍과 A.5의 종료 실행을 연결한다. 종료 결과에 관한 두 방향의 전제와 결론을 구분한다. |
| 11 | 대입 규칙이 참조하는 식 평가·갱신은 A.2–A.3을 사용한다. 단언의 치환과 상태 갱신을 잇는 보조정리를 여기에 배치한다. |
| 12 | 반복 불변식에서 프로그램 가드의 불 값과 상태에 관한 수학적 명제를 구별한다. 단언의 곱셈은 산술식 문법을 확장하지 않는다. |
| 13 | 변량은 상태에 관한 수학적 함수로 둔다. 프로그램 안의 뺄셈과 파생 조건식의 해석은 A.1·A.4를 따른다. |
