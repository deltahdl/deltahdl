#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_diagnosed.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"

using namespace delta;

struct ArrayKind {
  int array_type = vpiStaticArray;
  bool four_state = true;
};

class VpiValueArraySimBase : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiHandle MakeArray(std::string_view name,
                      const std::vector<std::vector<int>>& dims, int count,
                      uint32_t elem_width, ArrayKind kind = {}) {
    elems_.clear();
    name_pool_.reserve(name_pool_.size() + count);
    for (int i = 0; i < count; ++i) {
      auto* v = sim_ctx_.CreateVariable(
          name_pool_.emplace_back(std::string(name) + std::to_string(i)),
          elem_width);
      v->is_4state = kind.four_state;
      elems_.push_back(v);
    }
    return vpi_ctx_.CreateRegArray(name, kind.array_type, dims, elems_);
  }

  void SetElem(int i, uint64_t aval, uint64_t bval = 0) {
    elems_[i]->value.words[0].aval = aval;
    elems_[i]->value.words[0].bval = bval;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  Diagnosed diagnosed_{diag_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
  std::vector<Variable*> elems_;
  std::vector<std::string> name_pool_;
};
