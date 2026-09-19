#pragma once

#include <gtest/gtest.h>

#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

using namespace delta;

// A VpiContext installed as the global one for the test, with one way of
// leaving an error status pending in it, which is what the §38.1 argument
// conventions and the §38.2 error-checking tests both start from.
class VpiErrorRaisingFixture : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // §38.2: drive a VPI routine into its error path so an error status is
  // pending. vpi_register_systf() rejects a name that does not begin with a
  // dollar sign and records a vpiError-level error (§36.9.1 / §38.37.1).
  void RaiseError() {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("missing_dollar");
    vpi_register_systf(&data);
  }

  VpiContext vpi_ctx_;
};
