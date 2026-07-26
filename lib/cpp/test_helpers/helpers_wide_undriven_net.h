#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

// Elaborates and runs a module whose only declaration is one undriven 96-bit
// net of type `net_type`, then checks every bit of the value the resolver left
// on it: `bit_value` is the level each bit carries, and no bit is unknown.
// Returns the settled net, so a caller goes on to read the strength that
// accompanied the value.
//
// A net type whose undriven value is not z fills its whole width from that
// value, and a vector wider than one machine word is what shows the fill
// reaches every word rather than only the first. Returns nullptr when the
// module did not elaborate or declared no such net.
inline Net* ExpectWideUndrivenNetBits(SimFixture& f, const char* net_type,
                                      bool bit_value) {
  auto* design = ElaborateSrc(
      "module m;\n  " + std::string(net_type) + " [95:0] w;\nendmodule\n", f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return nullptr;
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  EXPECT_NE(w, nullptr);
  if (w == nullptr) return nullptr;

  const auto& v = w->resolved->value;
  EXPECT_GT(v.nwords, 1u);
  for (uint32_t i = 0; i < v.nwords; ++i) {
    uint32_t bits = 96 - i * 64;
    uint64_t mask = bits >= 64 ? ~uint64_t{0} : (uint64_t{1} << bits) - 1;
    EXPECT_EQ(v.words[i].aval & mask, bit_value ? mask : 0u) << i;
    EXPECT_EQ(v.words[i].bval & mask, 0u) << i;
  }
  return w;
}
