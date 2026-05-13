#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.22 main body's own normative rules — "the scope of a data type
// identifier shall include the hierarchical instance scope", "each instance
// with a user-defined type declared inside the instance creates a unique
// type", and the package/compilation-unit import requirement for type
// matching across instances — are covered by tests under their narrower
// subclauses (§6.22.1 matching, §6.22.2 equivalence). Assignment
// compatibility tests that previously lived here have been moved to
// test_elaborator_clause_06_22_03.cpp where §6.22.3 owns the rule.

}  // namespace
