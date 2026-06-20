#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

using namespace delta;

// Shared base fixture for the vpi_get_value_array / vpi_put_value_array tests.
// It installs a global VPI context for the duration of a test and offers a
// helper to build a static unpacked array of freshly created element variables,
// retaining the variable pointers so a test can install or read back element
// values that the value-array routines touch.
class VpiValueArraySimBase : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Build a static unpacked array with `count` freshly created element
  // variables (all bits initialized to x) and retain the variable pointers.
  VpiHandle MakeArray(std::string_view name,
                      const std::vector<std::vector<int>>& dims, int count,
                      uint32_t elem_width, int array_type = vpiStaticArray,
                      bool four_state = true) {
    elems_.clear();
    name_pool_.reserve(name_pool_.size() + count);
    for (int i = 0; i < count; ++i) {
      auto* v = sim_ctx_.CreateVariable(
          name_pool_.emplace_back(std::string(name) + std::to_string(i)),
          elem_width);
      v->is_4state = four_state;
      elems_.push_back(v);
    }
    return vpi_ctx_.CreateRegArray(name, array_type, dims, elems_);
  }

  // Install a known (aval, bval) into one element's first value word.
  void SetElem(int i, uint64_t aval, uint64_t bval = 0) {
    elems_[i]->value.words[0].aval = aval;
    elems_[i]->value.words[0].bval = bval;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
  std::vector<Variable*> elems_;
  std::vector<std::string> name_pool_;
};
