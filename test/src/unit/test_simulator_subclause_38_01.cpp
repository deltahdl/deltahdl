#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.1 General: the conventions the definitions of clause 38 are written in -
// the Synopsis, Syntax, Returns, Arguments and Related routines headings - and
// one rule about what those definitions mean: "All arguments shall be
// considered mandatory unless specifically noted in the definition of the PLI
// routine."
//
// So the clause is read against the routines rather than against any object of
// the model: a routine whose definition notes nothing about an argument has to
// be given it, and a call that omits one reports failure rather than acting on
// some default the caller never wrote. §38.2 is where the exception the
// sentence allows for is actually written - "If the error information is not
// needed, a NULL can be passed to the routine" - and §37.4.3 writes another,
// the relationships a data model diagram draws from a circle, which are
// traversed with NULL for the reference object. These tests observe both sides
// of the rule through the public entry points: routines that were given no
// argument, and the routines whose own definitions say that is allowed.

class VpiArgumentConventions : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // §38.2: drive a VPI routine into its error path so an error status is
  // pending. vpi_register_systf() rejects a name that does not begin with a
  // dollar sign and records a vpiError-level error (§36.9.1 / §38.37.1).
  void RaiseError() {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = "missing_dollar";
    vpi_register_systf(&data);
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// The rule: an argument no definition notes otherwise about is mandatory, so a
// call that omits one reports its failure return - a null handle, or zero -
// rather than proceeding on a value the caller never supplied.
TEST_F(VpiArgumentConventions, AnOmittedMandatoryArgumentMakesTheCallFail) {
  // §38.36: the s_cb_data describing the callback to register.
  EXPECT_EQ(vpi_register_cb(nullptr), nullptr);

  // §38.37: the s_vpi_systf_data describing the system task or function.
  EXPECT_EQ(vpi_register_systf(nullptr), nullptr);

  // §38.39: the handle to the callback to remove.
  EXPECT_EQ(vpi_remove_cb(nullptr), 0);

  // §38.17: the structure the product and version information is written into.
  EXPECT_EQ(vpi_get_vlog_info(nullptr), 0);

  // §38.3: the two handles to compare. Neither names an object, so they cannot
  // refer to the same one.
  EXPECT_EQ(vpi_compare_objects(nullptr, nullptr), 0);
}

// The exception, written in §38.2: "If the error information is not needed, a
// NULL can be passed to the routine." So vpi_chk_error() still reports the
// severity level of the pending error when given no structure to describe it
// in - the argument the definition notes is the one that may be left out, and
// the routine's answer does not depend on it.
TEST_F(VpiArgumentConventions, TheExceptionSection38_2NotesIsHonoured) {
  RaiseError();

  SVpiErrorInfo info = {};
  int with_structure = vpi_chk_error(&info);
  ASSERT_EQ(with_structure, vpiError);

  // §38.2: "Calling vpi_chk_error() shall have no effect on the error status",
  // so the same error is still pending and the null form reports it too.
  EXPECT_EQ(vpi_chk_error(nullptr), vpiError);
}

// The other exception, written in §37.4.3: a relationship a data model diagram
// draws from a circle "is traversed using NULL for the ref_h". §37.42 detail 3
// draws one to the system task or function call that invoked the application,
// and §37.80 detail 2 draws one to the callbacks no object reaches - so for
// those the reference object is the argument a definition notes may be NULL.
TEST_F(VpiArgumentConventions,
       AReferenceObjectMayBeOmittedWhereADiagramSaysSo) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  // §37.80 detail 2: the NULL-reference iteration is the one that reaches these
  // callbacks, so it hands back an iterator rather than refusing the call.
  EXPECT_NE(vpi_iterate(vpiCallback, nullptr), nullptr);

  // §37.42 detail 3: the traversal is defined with NULL, and reports no call
  // because no application is running inside one here - which is an answer, not
  // a refusal.
  EXPECT_EQ(vpi_handle(vpiSysTfCall, nullptr), nullptr);
}

// And where no definition notes it, the reference object is mandatory like any
// other argument: a relation the model draws from an object and never from a
// circle reaches nothing when asked without one.
TEST_F(VpiArgumentConventions, AReferenceObjectIsMandatoryWhereNoneSaysSo) {
  // §37.83 draws vpiParent from an attribute, §37.15 from a ref obj - never
  // from a circle.
  EXPECT_EQ(vpi_handle(vpiParent, nullptr), nullptr);

  // §37.14 draws a port iteration from the instance that declares the ports.
  EXPECT_EQ(vpi_iterate(vpiPort, nullptr), nullptr);
}

}  // namespace
}  // namespace delta
