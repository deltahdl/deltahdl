#include <gtest/gtest.h>

#include <cstdint>
#include <fstream>
#include <ios>
#include <string>

#include "common/types.h"
#include "fixture_sdf_design.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

std::string MtmDesign(const std::string& sdf_path) {
  return "module mtm_leaf(input X, output Y);\n"
         "  specify\n"
         "    (X => Y) = 0;\n"
         "  endspecify\n"
         "endmodule\n"
         "module dut;\n"
         "  logic y_out;\n"
         "  mtm_leaf u(1'b0, y_out);\n"
         "  initial $sdf_annotate(\"" +
         sdf_path +
         "\");\n"
         "endmodule\n";
}

uint64_t AnnotatedDelayUnderMode(const std::string& stem, DelayMode mode) {
  const std::string kSdfPath = "/tmp/delta_c32_09c_" + stem + ".sdf";
  std::ofstream sdf(kSdfPath, std::ios::trunc);
  sdf << "(DELAYFILE (CELL (CELLTYPE \"mtm_leaf\") (INSTANCE dut/u) "
         "(DELAY (ABSOLUTE (IOPATH X Y (41:52:63))))))";
  sdf.close();

  SdfDesign under_test;
  if (!under_test.Lower(MtmDesign(kSdfPath))) {
    ADD_FAILURE() << "the design did not reach the lowerer, so nothing ran";
    return 0;
  }
  SpecifyManager* installed = under_test.f.ctx.GetSpecifyManager();
  if (installed == nullptr) {
    ADD_FAILURE() << "the run installed no specify manager to annotate onto";
    return 0;
  }
  under_test.f.ctx.SetDelayMode(mode);
  under_test.f.scheduler.Run();

  for (const auto& pd : installed->GetPathDelays()) {
    if (pd.inst_prefix == "u." && pd.dst_port == "Y") return pd.delays[0];
  }
  ADD_FAILURE() << "instance u declared no module path ending at Y";
  return 0;
}

TEST(SdfToolControlMtm, AbsentMtmSpecAnnotatesTheMinimumWhenTheRunSelectsIt) {
  EXPECT_EQ(AnnotatedDelayUnderMode("min", DelayMode::kMin), 41u);
}

TEST(SdfToolControlMtm, AbsentMtmSpecAnnotatesTheMaximumWhenTheRunSelectsIt) {
  EXPECT_EQ(AnnotatedDelayUnderMode("max", DelayMode::kMax), 63u);
}

}  // namespace
