#pragma once

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

// Elaborates `src`, runs the full lower/schedule pipeline, and verifies that
// the source unpacked a 16'hABCD stream into byte targets `a` and `b`
// (a == 0xAB, b == 0xCD). Shared by the §11.4.14 streaming-unpack tests whose
// only difference is the source text driving the assignment.
inline void RunStreamUnpackAbcdIntoAB(SimFixture& f, const std::string& src) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xABu);
  EXPECT_EQ(vb->value.ToUint64(), 0xCDu);
}
