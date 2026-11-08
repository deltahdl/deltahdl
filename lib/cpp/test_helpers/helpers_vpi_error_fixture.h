#pragma once

#include <gtest/gtest.h>

#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

using namespace delta;

class VpiErrorRaisingFixture : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  void RaiseError() {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("missing_dollar");
    vpi_register_systf(&data);
  }

  VpiContext vpi_ctx_;
};
