#include <gtest/gtest.h>

#include <fstream>
#include <ios>
#include <string>
#include <string_view>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "helpers_sdf_delay_mapping.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

const char* GateCellText() {
  return "module gate_body(input b_in0, input b_in1, output b_out);\n"
         "  and #7 g_and(b_out, b_in0, b_in1);\n"
         "endmodule\n";
}

std::string SavedSdf(const std::string& stem, const std::string& text) {
  const std::string kName = "/tmp/delta_c32_04_01b_" + stem + ".sdf";
  std::ofstream sink(kName, std::ios::trunc);
  sink << text;
  sink.close();
  return kName;
}

std::string DeviceOnBOut(const std::string& instance_path,
                         const std::string& value) {
  return "(DELAYFILE (CELL (CELLTYPE \"gate_body\") (INSTANCE " +
         instance_path + ") (DELAY (ABSOLUTE (DEVICE b_out (" + value +
         "))))))";
}

const char* TimedCellText() {
  return "module gate_timed(input t_in0, input t_in1, output t_out);\n"
         "  specparam tgate = 13;\n"
         "  and #tgate g_timed(t_out, t_in0, t_in1);\n"
         "endmodule\n";
}

std::string LabelOnTGate(const std::string& instance_path,
                         const std::string& value) {
  return "(DELAYFILE (CELL (CELLTYPE \"gate_timed\") (INSTANCE " +
         instance_path + ") (LABEL (ABSOLUTE (tgate " + value + ")))))";
}

std::string TwoInstanceDesign(const std::string& sdf_path) {
  return TimedCellText() +
         std::string(
             "module gate_board;\n"
             "  logic first_out;\n"
             "  logic second_out;\n"
             "  gate_timed u_first(1'b0, 1'b1, first_out);\n"
             "  gate_timed u_second(1'b0, 1'b1, second_out);\n"
             "  initial $sdf_annotate(\"") +
         sdf_path + "\");\nendmodule\n";
}

SpecifyManager* ManagerOfRun(SdfDesign& design, const std::string& src) {
  if (!design.Lower(src)) return nullptr;
  SpecifyManager* installed = design.f.ctx.GetSpecifyManager();
  if (installed == nullptr) return nullptr;
  design.f.scheduler.Run();
  return installed;
}

const PrimitiveDriver* DriverFound(const SpecifyManager& mgr,
                                   std::string_view prefix,
                                   std::string_view port) {
  for (const auto& driver : mgr.GetPrimitiveDrivers()) {
    if (driver.inst_prefix == prefix && driver.output_port == port) {
      return &driver;
    }
  }
  return nullptr;
}

constexpr int kRiseSlot = 0;

TEST(GateDriverRegistration, RunningADesignRegistersItsGatesDriver) {
  SdfDesign design;
  SpecifyManager* mgr =
      ManagerOfRun(design,
                   "module gate_holder;\n"
                   "  logic hold_in0;\n"
                   "  logic hold_in1;\n"
                   "  logic hold_out;\n"
                   "  and #7 g_held(hold_out, hold_in0, hold_in1);\n"
                   "endmodule\n");
  ASSERT_NE(mgr, nullptr);

  const PrimitiveDriver* held = DriverFound(*mgr, "", "hold_out");
  ASSERT_NE(held, nullptr);
  EXPECT_EQ(held->delays[kRiseSlot], 7u);
}

TEST(GateDriverRegistration, DeviceEntryAnnotatesTheRegisteredGate) {
  const std::string kSdf =
      SavedSdf("single", DeviceOnBOut("gate_wrap/u_sole", "19"));

  SdfDesign design;
  SpecifyManager* mgr = ManagerOfRun(
      design, GateCellText() +
                  std::string("module gate_wrap;\n"
                              "  logic wrap_out;\n"
                              "  gate_body u_sole(1'b0, 1'b1, wrap_out);\n"
                              "  initial $sdf_annotate(\"") +
                  kSdf + "\");\nendmodule\n");
  ASSERT_NE(mgr, nullptr);

  const PrimitiveDriver* annotated = DriverFound(*mgr, "u_sole.", "b_out");
  ASSERT_NE(annotated, nullptr);
  EXPECT_EQ(annotated->delays[kRiseSlot], 19u);
}

TEST(GateDriverRegistration, DeviceEntryLeavesTheUnnamedInstancesGateAlone) {
  const std::string kSdf =
      SavedSdf("pair", DeviceOnBOut("gate_pair/u_named", "31"));

  SdfDesign design;
  SpecifyManager* mgr = ManagerOfRun(
      design, GateCellText() +
                  std::string("module gate_pair;\n"
                              "  logic named_out;\n"
                              "  logic other_out;\n"
                              "  gate_body u_named(1'b0, 1'b1, named_out);\n"
                              "  gate_body u_other(1'b0, 1'b1, other_out);\n"
                              "  initial $sdf_annotate(\"") +
                  kSdf + "\");\nendmodule\n");
  ASSERT_NE(mgr, nullptr);

  const PrimitiveDriver* named = DriverFound(*mgr, "u_named.", "b_out");
  ASSERT_NE(named, nullptr);
  EXPECT_EQ(named->delays[kRiseSlot], 31u);
  const PrimitiveDriver* other = DriverFound(*mgr, "u_other.", "b_out");
  ASSERT_NE(other, nullptr);
  EXPECT_EQ(other->delays[kRiseSlot], 7u);
}

TEST(GateDriverSpecparamRebuild, LabelReachesTheNamedInstancesGateDelay) {
  const std::string kSdf =
      SavedSdf("label_named", LabelOnTGate("gate_board/u_second", "23"));

  SdfDesign design;
  SpecifyManager* mgr = ManagerOfRun(design, TwoInstanceDesign(kSdf));
  ASSERT_NE(mgr, nullptr);

  const PrimitiveDriver* named = DriverFound(*mgr, "u_second.", "t_out");
  ASSERT_NE(named, nullptr);
  EXPECT_EQ(named->delays[kRiseSlot], 23u);
}

TEST(GateDriverSpecparamRebuild,
     LabelLeavesTheOtherInstancesGateDelayDeclared) {
  const std::string kSdf =
      SavedSdf("label_other", LabelOnTGate("gate_board/u_second", "29"));

  SdfDesign design;
  SpecifyManager* mgr = ManagerOfRun(design, TwoInstanceDesign(kSdf));
  ASSERT_NE(mgr, nullptr);

  const PrimitiveDriver* other = DriverFound(*mgr, "u_first.", "t_out");
  ASSERT_NE(other, nullptr);
  EXPECT_EQ(other->delays[kRiseSlot], 13u);
}

TEST(GateDriverSpecparamRebuild,
     RebuildReplacesTheInstanceDriverRatherThanAddingOne) {
  const std::string kSdf =
      SavedSdf("label_count", LabelOnTGate("gate_board/u_second", "41"));

  SdfDesign design;
  SpecifyManager* mgr = ManagerOfRun(design, TwoInstanceDesign(kSdf));
  ASSERT_NE(mgr, nullptr);

  EXPECT_EQ(mgr->GetPrimitiveDrivers().size(), 2u);
}

std::string AndCellRun(const std::string& sdf_path) {
  return "module and_cell(input a, input b, output y);\n"
         "  and #1 g1(y, a, b);\n"
         "endmodule\n"
         "module top;\n"
         "  reg a, b;\n"
         "  wire yo;\n"
         "  and_cell u1(.a(a), .b(b), .y(yo));\n"
         "  initial $sdf_annotate(\"" +
         sdf_path +
         "\");\n"
         "  always @(yo) if ($time > 40) $display(\"yo=%0d at %0t\", yo, "
         "$time);\n"
         "  initial begin\n"
         "    a = 0; b = 1;\n"
         "    #50 a = 1;\n"
         "    #50 a = 0;\n"
         "  end\n"
         "endmodule\n";
}

std::string WriteAndCellSdf(const std::string& name,
                            const std::string& device) {
  const std::string kPath = "/tmp/delta_c32_04_01b_" + name + ".sdf";
  std::ofstream out(kPath, std::ios::trunc);
  out << "(DELAYFILE (CELL (CELLTYPE \"and_cell\") (INSTANCE top/u1) (DELAY "
         "(ABSOLUTE "
      << device << "))))";
  return kPath;
}

TEST(SdfGateDeviceRun, DeviceEntryTimesTheGateDrivingTheOutput) {
  SimFixture whole;
  EXPECT_EQ(
      RunCapture(AndCellRun(WriteAndCellSdf("whole", "(DEVICE (7) (13))")),
                 whole),
      "yo=1 at 57\nyo=0 at 113\n");
  SimFixture port;
  EXPECT_EQ(
      RunCapture(AndCellRun(WriteAndCellSdf("port", "(DEVICE y (7) (13))")),
                 port),
      "yo=1 at 57\nyo=0 at 113\n");
}

TEST(SdfDelayMapping, ConditionalIopathReachesEveryPathWithItsCondition) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(
      "module k(input clk, input en, input d, output q);\n"
      "  specify\n"
      "    if (en) (posedge clk => (q +: d)) = 3;\n"
      "    if (en) (negedge clk => (q -: d)) = 4;\n"
      "  endspecify\n"
      "endmodule\n",
      f, mgr));

  AnnotateFileOnto(DelaySdf("(COND en (IOPATH clk q (9)))"), mgr);

  int reached = 0;
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == "clk" && pd.dst_port == "q") {
      EXPECT_EQ(pd.delays[0], 9u);
      ++reached;
    }
  }
  EXPECT_EQ(reached, 2);
}

TEST(SdfDeviceFallback, NoOperandDeviceReachesOnlyOutputDrivingGates) {
  const std::string kSdf =
      SavedSdf("internal_gate",
               "(DELAYFILE (CELL (CELLTYPE \"gate_pair\") (INSTANCE gate_top/u)"
               " (DELAY (ABSOLUTE (DEVICE (7))))))");
  SdfDesign design;
  SpecifyManager* mgr = ManagerOfRun(design,
                                     "module gate_pair(input a, output y);\n"
                                     "  wire n;\n"
                                     "  and #2 g1(n, a, a);\n"
                                     "  buf #3 g2(y, n);\n"
                                     "endmodule\n"
                                     "module gate_top;\n"
                                     "  logic a_in;\n"
                                     "  logic y_out;\n"
                                     "  gate_pair u(a_in, y_out);\n"
                                     "  initial $sdf_annotate(\"" +
                                         kSdf + "\");\nendmodule\n");
  ASSERT_NE(mgr, nullptr);
  const PrimitiveDriver* internal = DriverFound(*mgr, "u.", "n");
  const PrimitiveDriver* output = DriverFound(*mgr, "u.", "y");
  ASSERT_NE(internal, nullptr);
  ASSERT_NE(output, nullptr);
  EXPECT_EQ(internal->delays[kRiseSlot], 2u);
  EXPECT_EQ(output->delays[kRiseSlot], 7u);
}

TEST(SdfDeviceFallback, OperandNamingAnInstanceReachesItsPaths) {
  const std::string kSdf =
      SavedSdf("device_instance",
               "(DELAYFILE (CELL (CELLTYPE \"dev_top\") (INSTANCE dev_top)"
               " (DELAY (ABSOLUTE (DEVICE u1 (7))))))");
  SdfDesign design;
  SpecifyManager* mgr = ManagerOfRun(design,
                                     "module dev_leaf(input a, output y);\n"
                                     "  specify\n"
                                     "    (a => y) = 5;\n"
                                     "  endspecify\n"
                                     "endmodule\n"
                                     "module dev_top;\n"
                                     "  logic a_in;\n"
                                     "  logic y_out;\n"
                                     "  dev_leaf u1(a_in, y_out);\n"
                                     "  initial $sdf_annotate(\"" +
                                         kSdf + "\");\nendmodule\n");
  ASSERT_NE(mgr, nullptr);
  int reached = 0;
  for (const auto& pd : mgr->GetPathDelays()) {
    if (pd.inst_prefix != "u1.") continue;
    EXPECT_EQ(pd.delays[kRiseSlot], 7u);
    ++reached;
  }
  EXPECT_EQ(reached, 1);
}

TEST(SdfDeviceFallback, OperandNamingAnInstanceOutputReachesItsPaths) {
  const std::string kSdf =
      SavedSdf("device_instance_output",
               "(DELAYFILE (CELL (CELLTYPE \"dev2_top\") (INSTANCE dev2_top)"
               " (DELAY (ABSOLUTE (DEVICE u1/y (7))))))");
  SdfDesign design;
  SpecifyManager* mgr =
      ManagerOfRun(design,
                   "module dev2_leaf(input a, output y, output z);\n"
                   "  specify\n"
                   "    (a => y) = 5;\n"
                   "    (a => z) = 6;\n"
                   "  endspecify\n"
                   "endmodule\n"
                   "module dev2_top;\n"
                   "  logic a_in;\n"
                   "  logic y_out;\n"
                   "  logic z_out;\n"
                   "  dev2_leaf u1(a_in, y_out, z_out);\n"
                   "  initial $sdf_annotate(\"" +
                       kSdf + "\");\nendmodule\n");
  ASSERT_NE(mgr, nullptr);
  for (const auto& pd : mgr->GetPathDelays()) {
    if (pd.inst_prefix != "u1.") continue;
    EXPECT_EQ(pd.delays[kRiseSlot], pd.dst_port == "y" ? 7u : 6u)
        << pd.dst_port;
  }
}

}  // namespace
