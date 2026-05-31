#include <gtest/gtest.h>

#include "elaborator/checker_variable_assignment.h"
#include "fixture_checker_elab.h"

using namespace delta;

namespace {

// §17.7.1: a checker holding a non-free variable with a continuous assignment
// elaborates into a module carrying that variable and that assign.
TEST(CheckerElab, ElaborateCheckerWithVars) {
  CheckerElabFixture f;
  auto* design = ElaborateSource(
      "checker my_chk;\n"
      "  logic [7:0] count;\n"
      "  assign count = 8'hFF;\n"
      "endchecker\n",
      f, "my_chk");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->name, "my_chk");
  EXPECT_FALSE(mod->variables.empty());
  EXPECT_FALSE(mod->assigns.empty());
}

// §17.7.1: checker variables may be assigned using blocking and nonblocking
// procedural assignments, or non-procedural continuous assignments — each form
// is available.
TEST(CheckerVariableAssignment, AllThreeAssignmentFormsAreAvailable) {
  EXPECT_TRUE(CheckerVariableAssignmentFormIsAvailable(
      CheckerVariableAssignment::kBlockingProcedural));
  EXPECT_TRUE(CheckerVariableAssignmentFormIsAvailable(
      CheckerVariableAssignment::kNonblockingProcedural));
  EXPECT_TRUE(CheckerVariableAssignmentFormIsAvailable(
      CheckerVariableAssignment::kContinuous));
}

// §17.7.1: in an always_ff procedure, only nonblocking assignments are allowed;
// blocking procedural and continuous assignments are not.
TEST(CheckerVariableAssignment, AlwaysFfOnlyAdmitsNonblocking) {
  EXPECT_TRUE(AlwaysFfAdmitsCheckerVariableAssignment(
      CheckerVariableAssignment::kNonblockingProcedural));
  EXPECT_FALSE(AlwaysFfAdmitsCheckerVariableAssignment(
      CheckerVariableAssignment::kBlockingProcedural));
  EXPECT_FALSE(AlwaysFfAdmitsCheckerVariableAssignment(
      CheckerVariableAssignment::kContinuous));
}

// §17.7.1: referencing a checker variable through its hierarchical name in an
// assignment is illegal; a simple in-checker reference is legal.
TEST(CheckerVariableAssignment, HierarchicalNameReferenceIsIllegal) {
  EXPECT_TRUE(CheckerVariableAssignmentReferenceIsLegal(
      CheckerVariableReference::kSimpleName));
  EXPECT_FALSE(CheckerVariableAssignmentReferenceIsLegal(
      CheckerVariableReference::kHierarchicalName));
}

// §17.7.1: continuous assignments and blocking procedural assignments to a free
// checker variable are illegal; only the nonblocking procedural form is legal.
TEST(CheckerVariableAssignment, FreeVariableOnlyTakesNonblocking) {
  EXPECT_TRUE(FreeCheckerVariableAssignmentIsLegal(
      CheckerVariableAssignment::kNonblockingProcedural));
  EXPECT_FALSE(FreeCheckerVariableAssignmentIsLegal(
      CheckerVariableAssignment::kContinuous));
  EXPECT_FALSE(FreeCheckerVariableAssignmentIsLegal(
      CheckerVariableAssignment::kBlockingProcedural));
}

// §17.7.1: a checker variable may not be assigned in an initial procedure, but
// it may be initialized in its declaration.
TEST(CheckerVariableAssignment, InitialProcedureForbiddenDeclarationAllowed) {
  EXPECT_TRUE(CheckerVariableAssignmentSiteIsLegal(
      CheckerVariableAssignmentSite::kDeclarationInitializer));
  EXPECT_FALSE(CheckerVariableAssignmentSiteIsLegal(
      CheckerVariableAssignmentSite::kInitialProcedure));
}

// §17.7.1: the right-hand side of a checker variable assignment may contain the
// sequence method triggered.
TEST(CheckerVariableAssignment, RhsMayContainTriggered) {
  EXPECT_TRUE(CheckerVariableAssignmentRhsMayContainTriggered());
}

// §17.7.1: the left-hand side of a nonblocking assignment may contain a free
// checker variable.
TEST(CheckerVariableAssignment, NonblockingLhsMayBeFreeCheckerVariable) {
  EXPECT_TRUE(NonblockingAssignmentLhsMayBeFreeCheckerVariable());
}

}  // namespace
