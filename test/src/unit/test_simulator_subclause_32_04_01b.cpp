// Whether a run registers a design's gate primitives at all, and whether a
// §32.4.1 DEVICE delay reaches one once it has.
//
// §32.4.1 Table 32-1 has a DEVICE entry annotate the delay of the cell instance
// it stands under: an entry naming no port annotates every output of that
// instance, and an entry naming a port annotates the driver of that output. For
// a gate-level cell -- which is what SDF backannotation is mostly for -- that
// driver is a gate primitive rather than a module path, and §29.8 puts a UDP
// instance inside a module "in the same manner as gates". So
// SpecifyManager::AnnotateSdfDeviceDelay falls back from the module paths to
// the primitive drivers, and that fallback searches
// SpecifyManager::GetPrimitiveDrivers.
//
// Issue #3395 is that the fallback had nothing to search. Every driver in
// primitive_drivers_ had been put there by a test calling
// SpecifyManager::AddPrimitiveDriversFromGate, which no file under src/ called,
// so a design's own gates never reached the manager and the DEVICE row of
// Table 32-1 could not land in any run. The cases in
// test_simulator_subclause_32_04_01a.cpp cannot report that: each one registers
// the drivers itself, through the fixture in
// lib/cpp/test_fixtures/fixture_specify_manager.h, before annotating onto them.
//
// The three cases here run a design instead and ask what the run registered.
// Each reads SimContext::GetSpecifyManager -- the manager Lowerer::Lower filled
// -- rather than a manager of its own, because that is the only one a design's
// gates can have reached.
//
// Every gate here is declared `and #7`, and no annotated value is 7: a driver
// still holding its declaration reads 7, a driver the file reached reads the
// file's value, and a driver that was never registered is absent rather than
// reading anything. The annotated values are 19 for the single instance and 31
// for the named one of a pair, so the instance a DEVICE record did not name
// cannot pass by holding the value meant for the instance it did name. No case
// rests on 0, which is both what an unset delay slot holds and what a lookup
// that matched nothing would leave behind.
//
// The last three cases cover the §32.4.3 rebuild of those same drivers rather
// than the §32.4.1 annotation of them, and they are issue #3401's. A gate's
// propagation delay may be written as a specparam, and §32.4.3 has every
// expression reading a specparam reevaluated when an SDF LABEL annotates a
// value to it, so the rebuilt driver has to reach the gate of the instance
// whose specparam was annotated and no other instance's.
// SpecifyManager::ReplacePrimitiveDriver matched a driver by its output port
// alone, and SpecifyManager's gate_decls_ recorded a gate declaration with no
// instance beside it where path_decls_ recorded one, so a rebuild had no
// instance to file its driver back at and overwrote whichever instance's driver
// stood first.
//
// Those three run one further cell, gate_timed, whose gate delay is the
// specparam tgate declared at 13. A LABEL section names the second of its two
// instances and annotates tgate to 23 where the reading is the named instance's
// delay, to 29 where the reading is the sibling that must stay at 13, and to 41
// where the reading is how many drivers the manager holds. None of 13, 23, 29
// and 41 is 0, none is one of the 7, 19 and 31 the DEVICE cases write, and no
// two quantities a case tells apart share a value, so a driver holding its
// declaration, a driver holding the value meant for its sibling and a driver
// holding a value another case's SDF file supplied are three different
// readings.

#include <gtest/gtest.h>

#include <fstream>
#include <ios>
#include <string>
#include <string_view>

#include "fixture_sdf_design.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

// The gate-level cell every design below instantiates: one output port driven
// by one `and` gate carrying the §28.16 delay 7. The gate's output terminal is
// the cell's own output port, which is what a DEVICE entry naming that port
// has to reach.
const char* GateCellText() {
  return "module gate_body(input b_in0, input b_in1, output b_out);\n"
         "  and #7 g_and(b_out, b_in0, b_in1);\n"
         "endmodule\n";
}

// `text` saved where a $sdf_annotate call can open it, answering the path.
std::string SavedSdf(const std::string& stem, const std::string& text) {
  const std::string kName = "/tmp/delta_c32_04_01b_" + stem + ".sdf";
  std::ofstream sink(kName, std::ios::trunc);
  sink << text;
  sink.close();
  return kName;
}

// A whole SDF file holding one CELL record for the gate_body instance
// `instance_path`, whose DELAY section carries the single DEVICE entry that
// gives port b_out the delay `value`. `instance_path` is written with the '/'
// dividers §32.9 gives an SDF instance path.
std::string DeviceOnBOut(const std::string& instance_path,
                         const std::string& value) {
  return "(DELAYFILE (CELL (CELLTYPE \"gate_body\") (INSTANCE " +
         instance_path + ") (DELAY (ABSOLUTE (DEVICE b_out (" + value +
         "))))))";
}

// The cell the §32.4.3 cases instantiate: one output port driven by one `and`
// gate whose §28.16 delay is not a literal but the specparam tgate, declared at
// 13. §6.20.5 permits a specparam "both within the specify block (see
// Clause 30) and in the main module body" and requires of the second site only
// that the declaration "be declared before it is referenced", which is the site
// used here: the gate reading tgate is a module item, so the cell needs no
// specify block and declares no module path at all.
const char* TimedCellText() {
  return "module gate_timed(input t_in0, input t_in1, output t_out);\n"
         "  specparam tgate = 13;\n"
         "  and #tgate g_timed(t_out, t_in0, t_in1);\n"
         "endmodule\n";
}

// A whole SDF file whose one CELL record for the gate_timed instance
// `instance_path` carries a LABEL section annotating the value `value` to the
// specparam tgate. §32.4.3 has such a section carry new values for the
// specparams the cell its CELL record names declares.
std::string LabelOnTGate(const std::string& instance_path,
                         const std::string& value) {
  return "(DELAYFILE (CELL (CELLTYPE \"gate_timed\") (INSTANCE " +
         instance_path + ") (LABEL (ABSOLUTE (tgate " + value + ")))))";
}

// The design each §32.4.3 case runs: gate_timed instantiated twice inside
// gate_board, which annotates from `sdf_path`. gate_board is declared last, so
// SdfDesign::Lower elaborates it as the top and the SDF instance path of an
// instance declared in it begins "gate_board/".
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

// Lowers and runs `src`, answering the SpecifyManager the run installed, or
// null where the design never got that far. Lowerer::Lower is what registers a
// module instance's gates, so this manager -- and not SdfDesign::mgr, which
// nothing here fills -- is where a design's own drivers are.
SpecifyManager* ManagerOfRun(SdfDesign& design, const std::string& src) {
  if (!design.Lower(src)) return nullptr;
  SpecifyManager* installed = design.f.ctx.GetSpecifyManager();
  if (installed == nullptr) return nullptr;
  design.f.scheduler.Run();
  return installed;
}

// The driver of output port `port` registered under the instance whose
// hierarchical prefix is `prefix`, or null where the run registered none. Both
// fields are needed: §28.4 has a gate name its terminals by the enclosing
// module's own names, so two instances of one cell drive a port spelled alike.
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

// The transition slot every case reads. A gate carrying one delay expression
// has FillPrimitiveDriverDelays (src/simulator/specify.cpp) put that value in
// slot 0 and spread it over the rest, and a DEVICE entry carrying one value
// reduces to three state transition delays that are all that value, which
// ApplySdfDeviceThreeStateValues likewise writes into slot 0 first. So slot 0
// carries the declaration before annotation and the file's value after it,
// with no expansion rule standing between the number written and the number
// read.
constexpr int kRiseSlot = 0;

// §32.4.1: a design's gate primitive is registered by running the design, so a
// DEVICE delay has something to fall back to. This is the reading issue #3395
// names: with no caller under src/ for
// SpecifyManager::AddPrimitiveDriversFromGate, this lookup answered null in
// every run, whatever gates the design declared.
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

// §32.4.1 Table 32-1: a DEVICE entry naming an output port annotates the delay
// of the primitive driving it, so the gate ends up holding the file's 19 rather
// than the 7 it was declared with. This is what says the registration reached
// SpecifyManager::AnnotateSdfDeviceDelay and not merely the manager: the driver
// existing proves the fallback has something to search, and only the value
// proves the search found it.
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

// §32.4.1 with §32.9's CELL record: the record names one of the two instances
// of the cell, so that instance's gate takes 31 while the other keeps the 7 its
// gate was declared with. PrimitiveDriver::inst_prefix is the only thing
// separating the two, both gates driving a port named b_out, so this is the
// case that decides whether registration carried the instance rather than only
// the gate.
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

// §32.4.3: a LABEL section annotates to the specparams of the cell instance its
// CELL record names, and an expression reading one of them is reevaluated, so
// the gate whose propagation delay is written as tgate ends up carrying the
// delay the annotated 23 produces rather than the 13 its declaration produced.
// The reevaluation is where the instance is needed twice over: tgate is read by
// its bare name, and the driver the reevaluation produces has to be filed back
// at the instance whose gate it came from.
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

// §32.4.3 with §32.9's CELL record: the LABEL section belongs to the instance
// its CELL record names, so annotating tgate in one of the two instances of
// gate_timed leaves the other instance's gate carrying the 13 the cell
// declared. Both gates drive an output spelled t_out and both read a specparam
// spelled tgate, so PrimitiveDriver::inst_prefix is the whole of what keeps the
// rebuilt driver off the sibling.
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

// §32.4.3: reevaluating a gate delay expression that reads an annotated
// specparam replaces the driver the gate already registered rather than adding
// a second one beside it. The design registers one driver per instance, so it
// still holds two after the annotation; a rebuild filed under a prefix no
// instance carries would leave both originals standing and append a third,
// which reading a delay off either instance would not show.
TEST(GateDriverSpecparamRebuild,
     RebuildReplacesTheInstanceDriverRatherThanAddingOne) {
  const std::string kSdf =
      SavedSdf("label_count", LabelOnTGate("gate_board/u_second", "41"));

  SdfDesign design;
  SpecifyManager* mgr = ManagerOfRun(design, TwoInstanceDesign(kSdf));
  ASSERT_NE(mgr, nullptr);

  EXPECT_EQ(mgr->GetPrimitiveDrivers().size(), 2u);
}

}  // namespace
