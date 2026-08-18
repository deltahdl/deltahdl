// Tests for IEEE 1800-2023 §33.2 "Overview".
//
// The subclause says what a configuration is for: it is an explicit set of
// rules specifying the exact source description used to represent each instance
// in a design, and selecting that source representation is called binding the
// instance. It adds that a design description starts at a top-level module,
// that the instantiated children are found from it, that the source
// descriptions of those children are located in turn, and that this continues
// until every instance in the design is mapped to a source description.
//
// The elaborator file beside this one covers the other thing §33.2 says, that a
// config is a design element in the SystemVerilog name space, and the §33.4 and
// §33.6 files cover which description each clause selects. What is left is the
// claim those rest on: that the description a configuration selects is the one
// that represents the instance when the design runs. Reading a binding off an
// elaborated design shows which description was chosen; only running it shows
// that the chosen one is what the instance does.
//
// So the two descriptions here differ in what they do rather than only in the
// library they came from, which is how §33.2's own example is written -- an RTL
// adder in one file and a gate-level adder in another. Each configuration below
// is paired with the same design under the same default clause with the
// instance clause struck out, since a binding the default clause would have
// produced anyway shows nothing about the clause that was meant to move it.

#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <string>
#include <string_view>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_library_design.h"
#include "fixture_scratch_dir.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// Each description lives in the library its own file name earns it, so nothing
// below writes a library onto a cell.
constexpr const char* kMapText =
    "library rtlLib top.v;\n"
    "library aLib adder.v;\n"
    "library gateLib adder.vg;\n";

// The cell topping the design instantiates the adder twice, so a configuration
// can move one binding and leave its sibling alone.
constexpr const char* kTopSource =
    "module top;\n"
    "  adder a1();\n"
    "  adder a2();\n"
    "endmodule\n";

// adder.v: the RTL description, and the cell it instantiates a level further
// down. Each says which description it is, beside the instance it stands in, so
// an instance running the wrong description cannot report the right line.
constexpr const char* kRtlAdderSource =
    "module adder;\n"
    "  sub s();\n"
    "  initial $display(\"%m rtl-adder\");\n"
    "endmodule\n"
    "module sub;\n"
    "  initial $display(\"%m rtl-sub\");\n"
    "endmodule\n";

// adder.vg: the gate-level description of the same two cells, differing from
// the RTL one in what it does.
constexpr const char* kGateAdderSource =
    "module adder;\n"
    "  sub s();\n"
    "  initial $display(\"%m gate-adder\");\n"
    "endmodule\n"
    "module sub;\n"
    "  initial $display(\"%m gate-sub\");\n"
    "endmodule\n";

// The configuration under test: it tops the design out in rtlLib, takes the RTL
// descriptions by default, and moves the second adder to the gate-level
// library.
constexpr const char* kSelectingConfig =
    "config cfg1;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  instance top.a2 liblist gateLib;\n"
    "endconfig\n";

// Its companion: the same configuration with the instance clause struck out,
// which is the answer that clause displaces.
constexpr const char* kPlainConfig =
    "config cfg2;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "endconfig\n";

// The assembled compilation unit of a mapped multi-file design, carrying the
// simulator state its run needs. What a configuration binds is read here by
// running the design rather than by inspecting it.
struct BoundDesign : LibraryDesign {
  Scheduler scheduler{arena};
  SimContext ctx{scheduler, arena, diag};
};

// Writes the library map and the three source descriptions, loading the map
// before any of them so every cell is tagged through it.
bool BuildExampleDesign(ScratchDir& tmp, BoundDesign& design) {
  auto map_path = tmp.Write("lib.map", kMapText);
  if (!design.map.LoadMapFile(map_path)) return false;
  if (!design.Add(tmp, "adder.v", kRtlAdderSource)) return false;
  if (!design.Add(tmp, "adder.vg", kGateAdderSource)) return false;
  return design.Add(tmp, "top.v", kTopSource);
}

// Parses `config_text`, elaborates the configuration `name` names with the
// map's search order installed, lowers the bound hierarchy and runs it,
// returning what the run wrote to stdout. Installing the map's order leaves the
// configuration's clauses something to override, so a clause being obeyed is
// distinguishable from a map order that happened to agree.
std::string RunConfigured(ScratchDir& tmp, BoundDesign& design,
                          const std::string& config_text,
                          std::string_view name) {
  if (!design.Add(tmp, "cfg.sv", config_text)) return "";
  const auto* cfg = design.ConfigNamed(name);
  if (cfg == nullptr) return "";
  Elaborator elab(design.arena, design.diag, design.unit);
  elab.SetLibraryDeclarationOrder(design.map.ResolveSearchOrder({}));
  auto* elaborated = elab.Elaborate(cfg);
  if (elaborated == nullptr) return "";
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  Lowerer lowerer(design.ctx, design.arena, design.diag);
  lowerer.Lower(elaborated);
  design.scheduler.Run();
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// Whether `line` appears in `out`. The instances report at the same simulation
// time and in no order the subclause fixes, so each claim is read as the
// presence of its own line.
bool Reports(const std::string& out, const std::string& line) {
  return out.find(line) != std::string::npos;
}

// §33.2: a configuration specifies the exact source description used to
// represent each instance, and the instance runs what it was bound to. The
// instance clause moves the second adder to the gate-level library, so the two
// instances of one cell run different descriptions in one design. An
// implementation binding both instances alike cannot report both lines.
TEST(ConfigSelectsTheRunningSource, EachInstanceRunsTheDescriptionBoundToIt) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  std::string out = RunConfigured(tmp, design, kSelectingConfig, "cfg1");
  EXPECT_TRUE(Reports(out, "top.a1 rtl-adder")) << out;
  EXPECT_TRUE(Reports(out, "top.a2 gate-adder")) << out;
}

// §33.2: the same design under the same default clause with the instance clause
// struck out. Both instances run the RTL description, which is the answer the
// instance clause displaces -- without this the case above would hold of a
// binding the default clause produced on its own.
TEST(ConfigSelectsTheRunningSource,
     StruckInstanceClauseLeavesBothInstancesOnTheDefault) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  std::string out = RunConfigured(tmp, design, kPlainConfig, "cfg2");
  EXPECT_TRUE(Reports(out, "top.a1 rtl-adder")) << out;
  EXPECT_TRUE(Reports(out, "top.a2 rtl-adder")) << out;
  EXPECT_FALSE(Reports(out, "gate-adder")) << out;
}

// §33.2: the source descriptions of the children are located in turn until
// every instance in the design is mapped to one. The cell each adder
// instantiates is a level below the instance the clause named, and it runs the
// description of the library its parent's binding carried down.
TEST(ConfigSelectsTheRunningSource,
     EveryInstanceBelowTheNamedOneRunsItsBoundDescription) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));
  std::string out = RunConfigured(tmp, design, kSelectingConfig, "cfg1");
  EXPECT_TRUE(Reports(out, "top.a1.s rtl-sub")) << out;
  EXPECT_TRUE(Reports(out, "top.a2.s gate-sub")) << out;
}

}  // namespace
