# 자동 검토가 멈췄을 때

정정 Issue, 원래 토론 댓글, 제안 PR은 GitHub에 남습니다. 관리자는 모델과 Actions를 모두 사용할 수 없는 동안에도 아래 명령으로 같은 대기열을 읽을 수 있습니다. 저장소 루트에서 GitHub CLI에 로그인한 상태로 실행합니다.

```sh
python3 scripts/reader_feedback.py --queue
```

각 항목의 `url`을 열어 원문을 읽습니다. `approved_file`이 있으면 대기열에서 원본 댓글과 대조한 저장소 원고입니다. 해당 리비전에서 파일의 SHA-256이 `file_sha256`과 같은지 확인합니다. 이미 사람이 작업 중인 변경안은 [열린 검토 PR](https://github.com/Maokami/pl-semantics-seminar/pulls?q=is%3Apr+is%3Aopen+label%3A%22reader+proposal%22)에서 확인합니다. 원고 수정과 검토 기록은 [공통 PR 절차](feedback-maintenance.ko.md#사람이-직접-고치는-경우)를 따릅니다. 로컬의 `bash scripts/verify.sh`는 결제나 Actions dispatch 없이 같은 검사를 실행합니다. 필요한 도구는 저장소에 고정한 Lean/Lake, Python 3, Node.js, GitHub CLI와 gh-aw v1.2.2입니다.

## 어디에서 멈췄는지 확인하기

| 관찰 | 관리자가 선택할 수 있는 경로 |
|---|---|
| GitHub 작업이 대기 중이거나 job을 하나도 시작하지 못함 | 실행의 annotation, [GitHub Status](https://www.githubstatus.com/), 동시 실행 중인 작업을 확인합니다. 이 공개 저장소의 표준 호스팅 러너 시간은 무료입니다. 계정의 결제 보류, 유료 러너, artifact/cache 저장 공간, 예산 중단은 [Billing & licensing](https://github.com/settings/billing)에서 구분합니다. 실제로 유료 사용이 차단됐다면 결제 수단과 해당 제품의 예산을 조정할 수 있습니다. 동시성·플랫폼 제한에는 대기 또는 지원 요청이 맞습니다. [공식 과금 기준](https://docs.github.com/en/billing/concepts/product-billing/github-actions) · [Actions 제한](https://docs.github.com/en/actions/reference/limits) |
| Claude API에서 429 또는 일시적 529 발생 | 429에서는 응답의 `retry-after`를 따르고 요청 빈도와 동시성을 낮춥니다. 529는 서비스 과부하이므로 복구 뒤 다시 시도합니다. API 크레딧 구매만으로 두 제한이 즉시 풀리지는 않습니다. [API 제한](https://platform.claude.com/docs/en/api/rate-limits) · [오류 코드](https://platform.claude.com/docs/en/api/errors) |
| Claude API의 잔액 또는 지출 한도 부족 | [Claude Console Billing](https://platform.claude.com/settings/billing)에서 해당 조직의 잔액을 확인하고 관리자가 크레딧을 구매할 수 있습니다. 조직·워크스페이스 spend limit에 걸렸다면 Console의 Limits도 확인합니다. 자동 충전은 별도 선택입니다. 키 오류나 권한 오류는 자격 증명과 조직을 먼저 확인합니다. [API 결제 안내](https://support.claude.com/en/articles/8977456-how-do-i-pay-for-my-claude-api-usage) |
| 로컬 Claude Code에서 구독 한도 도달 | [Claude Usage](https://claude.ai/settings/usage)에서 재설정 시각을 확인합니다. 기다리거나 사람이 직접 검토할 수 있습니다. 즉시 Claude를 계속 써야 한다면 지원되는 플랜에서 usage credits를 켜고 월 지출 한도를 정하거나, Claude Code에서 명시적으로 Console API 결제를 선택합니다. gh-aw는 저장소의 API 키로 실행됩니다. 구독의 추가 사용량 결제는 그 API 키의 잔액을 충전하지 않습니다. [구독 추가 사용량](https://support.claude.com/en/articles/12429409-manage-usage-credits-for-paid-claude-plans) · [Claude Code 결제 선택](https://support.claude.com/en/articles/11145838-use-claude-code-with-your-pro-max-or-ultra-plan) |
| 모델은 실행됐으나 글을 읽지 못했거나 PR이 생성되지 않음 | gh-aw 실행의 `agent`, `safe_outputs`, `conclusion`을 확인합니다. `DIFC-FILTERED`, `report_incomplete`, `missing_terminal_safe_output`은 그 자체로 사용량 소진을 뜻하지 않습니다. 원문 권한·승인 원고·출력 경로를 확인하거나 수동 대기열에서 처리합니다. |

## 비용을 들이지 않고 대기하거나 다시 시작하기

네 AI 워크플로는 API 키가 없거나 저장소 Actions 변수 `TEXTBOOK_AI_MODE`가 `manual`이면 모델 호출을 건너뛰고 작업 요약에 수동 경로를 남깁니다. 기본값은 `auto`입니다. 같은 워크플로·커밋에서 최근 24시간 이내 시작한 실패 실행이 있으면 자동 사건도 대기합니다. 이것은 저장소의 재시도 간격입니다. 실제 서비스의 한도 재설정 시각은 각 대시보드에 표시됩니다. GitHub 자체가 작업을 시작할 수 없으면 이 요약도 생성될 수 없으므로 위 CLI나 원래 GitHub 글을 사용합니다.

복구 후 관리자는 `TEXTBOOK_AI_MODE`를 `auto`로 되돌리고 필요한 워크플로 하나를 **Run workflow**로 실행할 수 있습니다. 사람이 요청한 실행은 실패 대기 시간을 건너뜁니다. 상태가 자동으로 유료 자격 증명으로 전환되지는 않습니다. 원래 피드백에 대한 검토·PR, 정확한 PR head의 검사, 병합 후 배포와 문단 링크를 순서대로 확인합니다. 로컬 빌드는 미리보기를 제공하며 GitHub의 필수 검사나 Pages 게시 완료를 대신 기록하지 않습니다.

## 필수 검사 적용

이 변경이 기본 브랜치에 반영된 뒤 사람 PR과 자동 제안 PR에서 `Textbook verification`이 실제 head에 생성되는지 확인합니다. Settings → Rules → Rulesets에서 `curriculum-v1.2` 대상 PR과 이 검사를 요구하도록 설정할 수 있습니다. 생성 전 이름을 필수화하면 이전 PR이 병합 대기 상태에 머물 수 있습니다. [GitHub 보호 브랜치](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches)
