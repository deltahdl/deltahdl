#include "elaborator/cover_pass_statement.h"

namespace delta {

bool CoverPassStatementAllows(CoverPassStatementForm form) {
  switch (form) {
    case CoverPassStatementForm::kConcurrentAssert:
    case CoverPassStatementForm::kConcurrentAssume:
    case CoverPassStatementForm::kConcurrentCover:
      return false;
    case CoverPassStatementForm::kOther:
      return true;
  }
  return false;
}

}  // namespace delta
