#include "elaborator/concurrent_assert_action.h"

namespace delta {

bool ConcurrentAssertActionBlockAllows(ActionBlockStatementForm form) {
  switch (form) {
    case ActionBlockStatementForm::kConcurrentAssert:
    case ActionBlockStatementForm::kConcurrentAssume:
    case ActionBlockStatementForm::kConcurrentCover:
      return false;
    case ActionBlockStatementForm::kImmediateAssertion:
    case ActionBlockStatementForm::kOther:
      return true;
  }
  return false;
}

}  // namespace delta
