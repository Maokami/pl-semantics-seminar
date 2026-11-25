# IMP 정의의 원전 대조

[커리큘럼 v1.2 부록 B](curriculum.ko.md)를 집필에 적용할 때의 기준이다. [영어 정본의 언어 카드](../verso/PLBook/LanguageCard.lean) A.1–A.6을 공통 참조로 사용한다. 이름은 문자열, 상태는 이름 전체에서 수학적 정수로 가는 함수다. 같은 상태와 조건식에는 하나의 불 값이 정해진다.

## 원전 대조

리비전 `a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01`에 고정했다. [공유 모듈](../verso/PLBook/IMP/Language.lean)은 아래 정의를 같은 생성자와 인자 순서로 옮겼다. [시범 장의 증명](../verso/PLBook/IMP/Determinacy.lean)은 이 모듈을 가져온다.

| 카드 | 포트 위치 | 대조 결과 |
|---|---|---|
| A.1–A.3 | [Imp 13–35](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L13-L35), [148–149](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L148-L149) | 네 생성자, 정수 평가, 한 이름만 바꾸는 갱신. 함수는 상태를 먼저 받는다. 같은 식 문법에 대한 평가 판단은 교재 자체 정의다. |
| A.4 | [Imp 73–104](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L73-L104), [116–121](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L116-L121) | 조건식 생성자 여섯, 명령 생성자 다섯. ≤와 논리곱은 기본형이고 <와 논리합은 파생형이다. |
| A.5 | [Imp 172–188](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L172-L188) | 종료 실행 규칙 여섯. 조건문은 가드가 정한 명령의 유도 한 개를 받는다. 두 따름정리는 그 선택을 각 불 값에서 계산해 얻는다. |
| A.6 | [Imp 297–312](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Imp.lean#L297-L312) · [Sequences 12–14](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Sequences.lean#L12-L14), [95–110](https://github.com/leanprover/LeroyCompilerVerificationCourse/blob/a2730e7f9228b9d7ecf4510f1f8652f2cae7ba01/LeroyCompilerVerificationCourse/Sequences.lean#L95-L110) | 한 걸음 규칙 여섯. 유한 경로는 길이 인자가 없는 귀납 관계다. 무한 경로는 자연수로 색인한 함수와 공귀납 술어가 모두 있다. |
