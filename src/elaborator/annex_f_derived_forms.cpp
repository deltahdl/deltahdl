#include "elaborator/annex_f_derived_forms.h"

#include "elaborator/annex_f_neutral_satisfaction.h"

namespace delta {

AssertionStatement::Role RoleOfConcurrentAssertionDirective(
    ConcurrentAssertionDirective directive) {
  switch (directive) {
    case ConcurrentAssertionDirective::kAssert:
      return AssertionStatement::Role::kAssert;
    case ConcurrentAssertionDirective::kCover:
      return AssertionStatement::Role::kCover;
    case ConcurrentAssertionDirective::kAssume:
    case ConcurrentAssertionDirective::kRestrict:
      return AssertionStatement::Role::kAssume;
  }
  return AssertionStatement::Role::kAssume;
}

}  // namespace delta
