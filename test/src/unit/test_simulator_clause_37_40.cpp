#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.40 Timing check: the object model diagram for a timing check (the "tchk"
// node) and its event terms (the "tchk term" node). The subclause carries two
// numbered Details. Detail 1 fixes what the vpiTchkRefTerm and vpiTchkDataTerm
// relations denote - the reference (or controlled-reference) event and the data
// event, the latter only when the check has one. Detail 2 fixes the types the
// vpiExpr iteration over a tchk returns - vpiTchkTerm for the event arguments
// and the natural expression type for every other argument. These tests observe
// the production code that applies those two rules through the public
// vpi_handle and vpi_iterate dispatch.

// The fixture installs a context so the public vpi_handle/vpi_iterate entry
// points run their real dispatch over the test objects.
class TimingCheck : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Detail 1: vpiTchkRefTerm reaches the timing check's reference (or
// controlled-reference) event term and vpiTchkDataTerm reaches its data event
// term. Both terms are tchk term objects, whose own type differs from the
// relation enum, so the relations resolve to the check's designated terms.
TEST_F(TimingCheck, RefAndDataTermsAreReached) {
  VpiObject ref_term;  // the reference / controlled-reference event
  ref_term.type = vpiTchkTerm;
  VpiObject data_term;  // the data event
  data_term.type = vpiTchkTerm;

  VpiObject tchk;
  tchk.type = vpiTchk;
  tchk.tchk_ref_term = &ref_term;
  tchk.tchk_data_term = &data_term;

  VpiHandle reached_ref = VpiHandleC(vpiTchkRefTerm, &tchk);
  VpiHandle reached_data = VpiHandleC(vpiTchkDataTerm, &tchk);
  EXPECT_EQ(reached_ref, &ref_term);
  EXPECT_EQ(reached_data, &data_term);

  // The handles returned for the events have the tchk term type.
  EXPECT_EQ(vpi_get(vpiType, reached_ref), vpiTchkTerm);
  EXPECT_EQ(vpi_get(vpiType, reached_data), vpiTchkTerm);
}

// Detail 1 ("if any"): a timing check that has no data event reports NULL for
// vpiTchkDataTerm, while its reference term is still reached.
TEST_F(TimingCheck, DataTermIsNullWhenCheckHasNoDataEvent) {
  VpiObject ref_term;
  ref_term.type = vpiTchkTerm;

  VpiObject tchk;
  tchk.type = vpiTchk;
  tchk.tchk_ref_term = &ref_term;
  // tchk_data_term left null: this check has no data event.

  EXPECT_EQ(VpiHandleC(vpiTchkRefTerm, &tchk), &ref_term);
  EXPECT_EQ(VpiHandleC(vpiTchkDataTerm, &tchk), nullptr);
}

// Detail 1 (scope): the vpiTchkRefTerm/vpiTchkDataTerm relations are specific
// to a timing check. On an object that is not a tchk, asking for them does not
// reach a stray tchk term, so the relations report NULL even when the object
// carries a tchk term child.
TEST_F(TimingCheck, TermRelationsApplyOnlyToTimingChecks) {
  VpiObject stray_term;
  stray_term.type = vpiTchkTerm;

  VpiObject not_a_tchk;
  not_a_tchk.type = vpiModule;
  not_a_tchk.children = {&stray_term};

  EXPECT_EQ(VpiHandleC(vpiTchkRefTerm, &not_a_tchk), nullptr);
  EXPECT_EQ(VpiHandleC(vpiTchkDataTerm, &not_a_tchk), nullptr);
}

// Detail 2: iterating vpiExpr over a timing check returns its arguments - the
// reference, controlled-reference, and data events as tchk term handles, and
// every other argument with the type of its expression. A non-argument child
// (the notifier register) is not reached by this relation.
TEST_F(TimingCheck, ExprIterationReturnsTermsAndExpressions) {
  VpiObject ref_term;  // a reference event -> vpiTchkTerm
  ref_term.type = vpiTchkTerm;
  VpiObject data_term;  // a data event -> vpiTchkTerm
  data_term.type = vpiTchkTerm;
  VpiObject limit;  // a limit argument expression -> its own expr type
  limit.type = vpiOperation;
  VpiObject notifier;  // the notifier register: not an expr argument
  notifier.type = vpiReg;

  VpiObject tchk;
  tchk.type = vpiTchk;
  tchk.tchk_ref_term = &ref_term;
  tchk.tchk_data_term = &data_term;
  tchk.children = {&ref_term, &notifier, &data_term, &limit};

  vpiHandle it = vpi_iterate(vpiExpr, &tchk);
  ASSERT_NE(it, nullptr);

  int count = 0;
  bool saw_ref = false;
  bool saw_data = false;
  bool saw_limit = false;
  bool saw_notifier = false;
  while (vpiHandle h = vpi_scan(it)) {
    ++count;
    if (h == &ref_term) saw_ref = true;
    if (h == &data_term) saw_data = true;
    if (h == &limit) saw_limit = true;
    if (h == &notifier) saw_notifier = true;
  }

  EXPECT_EQ(count, 3);
  EXPECT_TRUE(saw_ref);
  EXPECT_TRUE(saw_data);
  EXPECT_TRUE(saw_limit);
  EXPECT_FALSE(saw_notifier);  // the notifier reg is not an expr argument

  // The event arguments are returned with the tchk term type; the other
  // argument keeps the type of its expression.
  EXPECT_EQ(vpi_get(vpiType, &ref_term), vpiTchkTerm);
  EXPECT_EQ(vpi_get(vpiType, &data_term), vpiTchkTerm);
  EXPECT_EQ(vpi_get(vpiType, &limit), vpiOperation);
}

// Detail 2 (edge): a timing check whose only children are non-argument objects
// has nothing for the vpiExpr iteration to walk, so vpi_iterate reports a null
// handle rather than an iterator that scans to nothing.
TEST_F(TimingCheck, ExprIterationIsNullWhenNoArguments) {
  VpiObject notifier;
  notifier.type = vpiReg;

  VpiObject tchk;
  tchk.type = vpiTchk;
  tchk.children = {&notifier};

  EXPECT_EQ(vpi_iterate(vpiExpr, &tchk), nullptr);
}

}  // namespace
}  // namespace delta
