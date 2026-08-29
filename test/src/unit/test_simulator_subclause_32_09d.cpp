// Two instances of one cell under one SDF file, read apart.
//
// §32.4.1 has an IOPATH name its terminals by the cell's own port names, and
// §30.4 has the specify block that declares the matching module path name its
// terminals the same way, so every instance of a cell carries a module path
// spelled identically to every other instance's. What tells two of them apart
// is PathDelay::inst_prefix in src/simulator/specify_path_delay.h -- the
// hierarchical prefix of the instance, "u_left." for instance u_left of the
// top. §32.9's CELL record carries the instance the entries below it annotate,
// in its own INSTANCE field, so the two sides have a name each and the
// annotation is placeable.
//
// Issue #3387 is that it was not placed. AnnotateSdfIopathEntry in
// src/simulator/sdf_annotate.cpp built its PathDelay from the two port names
// and left inst_prefix empty, and SpecifyManager::AnnotateSdfPathDelay
// overwrote every entry carrying that port pair, so one IOPATH reached every
// in-scope instance of the cell and two instances of one cell both took the
// delay meant for one. No test in the tree could catch that: every §32.6 and
// §32.9 case put its module path in the module elaborated as the top, where
// there is one instance and the prefix is empty either way.
//
// Issue #3390 is the same defect in two further constructs.
// AnnotateSdfPulseLimitEntry handed SpecifyManager::AddSdfPulseLimit and
// SpecifyManager::IncrementSdfPulseLimit a port pair alone, and
// AnnotateSdfDeviceEntry handed SpecifyManager::AnnotateSdfDeviceDelay an
// output port alone, so a PATHPULSE record and a DEVICE record each reached
// every in-scope instance of the cell their own CELL record named.
//
// The five cases here are the ones that need the prefix -- two instances
// annotated apart, a module_instance operand that reaches one of them, an SDF
// instance path whose '/' dividers have to be read against a '.'-separated
// hierarchy, a PATHPULSE record placed on one of two instances, and a DEVICE
// record placed on one of two instances.
//
// Every design here declares its module path at 3, save the PATHPULSE one,
// which declares it at 90: §32.7 clamps a pulse limit to the delay it belongs
// to, so a limit annotated onto a path declared at 3 would come back as 3
// whichever instance it reached, and the two instances would read alike
// however the record was placed. Every annotated value is distinct from 3,
// from 90 and from every other value the file uses: 17 and 29 for the two
// instances one file annotates apart, 11 and 47 for the two the
// module_instance operand chooses between, 23 for the nested instance, 37 and
// 53 for the two instances a PATHPULSE record annotates apart, and 41 and 59
// for the two a DEVICE record does. So an instance that kept its declaration,
// an instance that took the other instance's value, and an instance annotated
// by a call that should not have reached it are three different readings. No
// case reads a value off a lookup that answers 0 when it finds nothing:
// PathUnder returns a pointer, which a case asserts on before reading through
// it.

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

// Puts `text` on disk under the name a $sdf_annotate call will open, and
// answers that name.
std::string SdfFileNamed(const std::string& stem, const std::string& text) {
  const std::string kPath = "/tmp/delta_c32_09d_" + stem + ".sdf";
  std::ofstream out(kPath, std::ios::trunc);
  out << text;
  out.close();
  return kPath;
}

// One CELL record for the delay_leaf instance `instance_path` names, carrying
// the single DELAY section entry `entry`. `instance_path` is written with the
// '/' dividers §32.9 gives an SDF instance path.
std::string LeafCellEntry(const std::string& instance_path,
                          const std::string& entry) {
  return " (CELL (CELLTYPE \"delay_leaf\") (INSTANCE " + instance_path +
         ") (DELAY (ABSOLUTE " + entry + ")))";
}

// The same record carrying an IOPATH that gives the instance's module path the
// delay `value`.
std::string LeafCell(const std::string& instance_path,
                     const std::string& value) {
  return LeafCellEntry(instance_path, "(IOPATH pin_i pin_o (" + value + "))");
}

// The design every case but the divider one runs: one cell declaring one
// module path with the delay `path_delay`, two instances of it, and a
// $sdf_annotate call whose operands `operands` writes. The top is named
// harness, so the scope a call naming no module_instance works from --
// SimContext::CurrentScopeName -- is "harness".
std::string PairDesign(const std::string& path_delay,
                       const std::string& operands) {
  return "module delay_leaf(input pin_i, output pin_o);\n"
         "  specify\n"
         "    (pin_i => pin_o) = " +
         path_delay +
         ";\n"
         "  endspecify\n"
         "endmodule\n"
         "module harness;\n"
         "  logic left_o;\n"
         "  logic right_o;\n"
         "  delay_leaf u_left(1'b0, left_o);\n"
         "  delay_leaf u_right(1'b0, right_o);\n"
         "  initial $sdf_annotate(" +
         operands +
         ");\n"
         "endmodule\n";
}

// The design the divider case runs: the same cell one level further down, so
// the instance the SDF names sits at harness.u_mid.u_inner and its SDF path
// carries a divider inside the part below the scope.
std::string NestedDesign(const std::string& operands) {
  return "module delay_leaf(input pin_i, output pin_o);\n"
         "  specify\n"
         "    (pin_i => pin_o) = 3;\n"
         "  endspecify\n"
         "endmodule\n"
         "module wrap_block(input w_i, output w_o);\n"
         "  delay_leaf u_inner(w_i, w_o);\n"
         "endmodule\n"
         "module harness;\n"
         "  logic deep_o;\n"
         "  wrap_block u_mid(1'b0, deep_o);\n"
         "  initial $sdf_annotate(" +
         operands +
         ");\n"
         "endmodule\n";
}

// A design lowered and run, holding on to the SpecifyManager the run installed:
// SimContext::GetSpecifyManager, which Lowerer::Lower filled through
// SimContext::AcquireSpecifyManager. That is the manager whose module paths
// carry the instance prefixes RegisterSpecifyBlocks in
// src/simulator/specify_register.cpp filed them under, so it is the only one
// these cases can read two instances apart in.
struct RunOfDesign {
  SdfDesign built;
  SpecifyManager* mgr = nullptr;

  bool Start(const std::string& src) {
    if (!built.Lower(src)) return false;
    mgr = built.f.ctx.GetSpecifyManager();
    if (mgr == nullptr) return false;
    built.f.scheduler.Run();
    return true;
  }

  // The module path the instance whose hierarchical prefix is `prefix`
  // declared, or null where the run registered none for that instance. Every
  // path here runs from pin_i to pin_o, so the prefix is the whole of what
  // separates one instance's path from another's.
  const PathDelay* PathUnder(std::string_view prefix) const {
    for (const auto& pd : mgr->GetPathDelays()) {
      if (pd.inst_prefix == prefix && pd.dst_port == "pin_o") return &pd;
    }
    return nullptr;
  }
};

// §32.4.1 with §32.9's CELL record: two CELL records naming the two instances
// of one cell give the same IOPATH different delays, and each instance ends up
// holding its own. This is the reading issue #3387 names: with the instance
// dropped, both paths would take whichever record was applied last.
TEST(SdfPerInstanceIopath, TwoInstancesOfOneCellTakeTheirOwnIopathDelays) {
  const std::string kSdf =
      SdfFileNamed("apart", "(DELAYFILE" + LeafCell("harness/u_left", "17") +
                                LeafCell("harness/u_right", "29") + ")");

  RunOfDesign run;
  ASSERT_TRUE(run.Start(PairDesign("3", "\"" + kSdf + "\"")));

  const PathDelay* left = run.PathUnder("u_left.");
  ASSERT_NE(left, nullptr);
  EXPECT_EQ(left->delays[0], 17u);
  const PathDelay* right = run.PathUnder("u_right.");
  ASSERT_NE(right, nullptr);
  EXPECT_EQ(right->delays[0], 29u);
}

// §32.9: the module_instance operand names a level of the hierarchy and the
// annotator works from that level down, so a call naming one of the two
// instances annotates that instance and leaves the other holding what it was
// declared with. The file carries a record for both, so an instance that read
// the record meant for the other reads 47 rather than 3.
TEST(SdfPerInstanceIopath, ModuleInstanceOperandNarrowsToTheInstanceItNames) {
  const std::string kSdf =
      SdfFileNamed("narrowed", "(DELAYFILE" + LeafCell("harness/u_left", "11") +
                                   LeafCell("harness/u_right", "47") + ")");

  RunOfDesign run;
  ASSERT_TRUE(run.Start(PairDesign("3", "\"" + kSdf + "\", harness.u_left")));

  const PathDelay* named = run.PathUnder("u_left.");
  ASSERT_NE(named, nullptr);
  EXPECT_EQ(named->delays[0], 11u);
  const PathDelay* unnamed = run.PathUnder("u_right.");
  ASSERT_NE(unnamed, nullptr);
  EXPECT_EQ(unnamed->delays[0], 3u);
}

// §32.9: an SDF instance path divides its levels with '/' while a SystemVerilog
// hierarchical name divides them with '.', so the instance a CELL record names
// is the instance harness.u_mid.u_inner however the file spells it. The
// instance sits two levels down, so the part of its path below the scope
// carries a divider of its own and the equivalence has to survive being written
// into a PathDelay::inst_prefix.
TEST(SdfPerInstanceIopath,
     SlashDividedInstancePathReachesADotSeparatedInstance) {
  const std::string kSdf = SdfFileNamed(
      "dividers", "(DELAYFILE" + LeafCell("harness/u_mid/u_inner", "23") + ")");

  RunOfDesign run;
  ASSERT_TRUE(run.Start(NestedDesign("\"" + kSdf + "\"")));

  const PathDelay* nested = run.PathUnder("u_mid.u_inner.");
  ASSERT_NE(nested, nullptr);
  EXPECT_EQ(nested->delays[0], 23u);
}

// §32.7 with §32.9's CELL record: two CELL records naming the two instances of
// one cell give the same PATHPULSE different limits, and each instance ends up
// holding its own rather than both holding whichever record was applied last.
// §30.7.1 has a lone reject limit stand as the error limit too, so both limits
// of both instances are read: a placement that reached the reject limit and
// left the error limit reaching every in-scope instance would pass a case that
// read only the reject limit.
TEST(SdfPerInstanceIopath, TwoInstancesOfOneCellTakeTheirOwnPathpulseLimits) {
  const std::string kSdf = SdfFileNamed(
      "pulse",
      "(DELAYFILE" +
          LeafCellEntry("harness/u_left", "(PATHPULSE pin_i pin_o (37))") +
          LeafCellEntry("harness/u_right", "(PATHPULSE pin_i pin_o (53))") +
          ")");

  RunOfDesign run;
  ASSERT_TRUE(run.Start(PairDesign("90", "\"" + kSdf + "\"")));

  const PathDelay* left = run.PathUnder("u_left.");
  ASSERT_NE(left, nullptr);
  EXPECT_EQ(left->reject_limit[0], 37u);
  EXPECT_EQ(left->error_limit[0], 37u);
  const PathDelay* right = run.PathUnder("u_right.");
  ASSERT_NE(right, nullptr);
  EXPECT_EQ(right->reject_limit[0], 53u);
  EXPECT_EQ(right->error_limit[0], 53u);
}

// §32.4.1 Table 32-1 with §32.9's CELL record: two CELL records naming the two
// instances of one cell give the same DEVICE different delays against the one
// module path each instance declares, and each instance ends up holding its
// own. The entry names the output port its cell's instance drives, which every
// instance of the cell has under that one name, so the instance the CELL record
// named is the whole of what separates the path the delay belongs to from the
// path it must leave alone.
TEST(SdfPerInstanceIopath, TwoInstancesOfOneCellTakeTheirOwnDeviceDelays) {
  const std::string kSdf = SdfFileNamed(
      "device",
      "(DELAYFILE" + LeafCellEntry("harness/u_left", "(DEVICE pin_o (41))") +
          LeafCellEntry("harness/u_right", "(DEVICE pin_o (59))") + ")");

  RunOfDesign run;
  ASSERT_TRUE(run.Start(PairDesign("3", "\"" + kSdf + "\"")));

  const PathDelay* left = run.PathUnder("u_left.");
  ASSERT_NE(left, nullptr);
  EXPECT_EQ(left->delays[0], 41u);
  const PathDelay* right = run.PathUnder("u_right.");
  ASSERT_NE(right, nullptr);
  EXPECT_EQ(right->delays[0], 59u);
}

}  // namespace
