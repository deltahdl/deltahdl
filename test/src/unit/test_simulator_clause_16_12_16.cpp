#include <gtest/gtest.h>

#include <vector>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.12.16: during the linear search the first item whose expression matches
// the case expression is the property statement that is evaluated, and the
// search terminates there. A later matching item with a different verdict is
// therefore never reached.
TEST(PropertyCase, FirstMatchingItemSelectedAndSearchTerminates) {
  std::vector<PropertyCaseBranch> branches = {
      {/*selected=*/false, PropertyResult::kFail},
      {/*selected=*/true, PropertyResult::kPass},
      {/*selected=*/true, PropertyResult::kFail},
  };
  EXPECT_EQ(EvalPropertyCase(branches, /*has_default=*/false,
                             PropertyResult::kFail),
            PropertyResult::kPass);
}

// §16.12.16: the verdict the case property returns is exactly that of the
// selected item's property_expr, including a failing one.
TEST(PropertyCase, SelectedItemVerdictPropagates) {
  std::vector<PropertyCaseBranch> branches = {
      {/*selected=*/false, PropertyResult::kPass},
      {/*selected=*/true, PropertyResult::kFail},
  };
  EXPECT_EQ(EvalPropertyCase(branches, /*has_default=*/false,
                             PropertyResult::kPass),
            PropertyResult::kFail);

  std::vector<PropertyCaseBranch> vacuous = {
      {/*selected=*/true, PropertyResult::kVacuousPass},
  };
  EXPECT_EQ(EvalPropertyCase(vacuous, /*has_default=*/false,
                             PropertyResult::kFail),
            PropertyResult::kVacuousPass);

  // An as-yet unresolved verdict from the selected item is carried through
  // unchanged rather than normalized — the case result tracks the chosen item.
  std::vector<PropertyCaseBranch> pending = {
      {/*selected=*/true, PropertyResult::kPending},
  };
  EXPECT_EQ(EvalPropertyCase(pending, /*has_default=*/false,
                             PropertyResult::kPass),
            PropertyResult::kPending);
}

// §16.12.16: if there is a default item it is ignored during the linear search.
// A matching ordinary item is taken even though a default is present, so the
// default verdict does not influence the result.
TEST(PropertyCase, DefaultIgnoredDuringLinearSearch) {
  std::vector<PropertyCaseBranch> branches = {
      {/*selected=*/false, PropertyResult::kFail},
      {/*selected=*/true, PropertyResult::kPass},
  };
  EXPECT_EQ(EvalPropertyCase(branches, /*has_default=*/true,
                             /*default_result=*/PropertyResult::kFail),
            PropertyResult::kPass);
}

// §16.12.16: if all comparisons fail and a default item is given, the default
// item's property statement is executed and provides the verdict.
TEST(PropertyCase, DefaultExecutedWhenAllComparisonsFail) {
  std::vector<PropertyCaseBranch> branches = {
      {/*selected=*/false, PropertyResult::kPass},
      {/*selected=*/false, PropertyResult::kPass},
  };
  EXPECT_EQ(EvalPropertyCase(branches, /*has_default=*/true,
                             /*default_result=*/PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyCase(branches, /*has_default=*/true,
                             /*default_result=*/PropertyResult::kPass),
            PropertyResult::kPass);
}

// §16.12.16: if the default item is not given and all comparisons fail, none of
// the item property statements is evaluated and the case property succeeds
// vacuously from that start point, returning true.
TEST(PropertyCase, NoDefaultAllComparisonsFailSucceedsVacuously) {
  std::vector<PropertyCaseBranch> branches = {
      {/*selected=*/false, PropertyResult::kFail},
      {/*selected=*/false, PropertyResult::kFail},
  };
  EXPECT_EQ(EvalPropertyCase(branches, /*has_default=*/false,
                             PropertyResult::kFail),
            PropertyResult::kVacuousPass);
}

}  // namespace
