#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/cover_results.h"
#include "simulator/cover_statement.h"

constexpr uint64_t kNoCover = ~uint64_t{0};

inline std::string SequenceCoverSource(const std::string& items,
                                       const std::string& drive,
                                       const std::string& outside = "") {
  return outside +
         "module t;\n"
         "  logic clk = 0;\n"
         "  logic te1 = 0, te2 = 0, te3 = 0, te4 = 0, te5 = 0;\n"
         "  int fails = 0;\n"
         "  int at = 0;\n"
         "  always #5 clk = ~clk;\n" +
         items + "  initial begin\n" + drive +
         "    #10 $finish;\n"
         "  end\n"
         "endmodule\n";
}

inline std::string DesignElementCoverSource(const std::string& statement,
                                            const std::string& drive) {
  std::string outside =
      "interface ifc(input logic clk, te1, te2, te3, te4, te5);\n"
      "  i1: ";
  outside += statement;
  outside +=
      "endinterface\n"
      "program pg(input logic clk, te1, te2, te3, te4, te5);\n"
      "  p1: ";
  outside += statement;
  outside +=
      "endprogram\n"
      "checker ck(logic clk, logic te1, logic te2, logic te3, logic te4,"
      " logic te5);\n"
      "  k1: ";
  outside += statement;
  outside += "endchecker\n";
  return SequenceCoverSource(
      "  ifc i(clk, te1, te2, te3, te4, te5);\n"
      "  pg p(clk, te1, te2, te3, te4, te5);\n"
      "  ck k(clk, te1, te2, te3, te4, te5);\n"
      "  if (1) begin : g\n"
      "    g1: " +
          statement + "  end\n",
      drive, outside);
}

inline void RunSequenceDesign(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

inline uint64_t CoverCount(SimFixture& f, const std::string& src,
                           std::string_view label) {
  uint32_t line = LineHolding(src, label);
  for (const auto& record : f.ctx.ConcurrentCovers().Results()) {
    if (record.line != line) continue;
    return record.category == CoverStatementCategory::kSequence
               ? record.matched
               : record.succeeded;
  }
  return kNoCover;
}

inline uint64_t VarValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? kNoCover : var->value.ToUint64();
}
