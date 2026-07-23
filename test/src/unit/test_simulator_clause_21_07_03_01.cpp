#include <algorithm>
#include <fstream>
#include <string>
#include <utility>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor (whose
// unwind path destroys the owned coverage database) is well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Exercises the $dumpports system task (§21.7.3.1) end to end: every test
// drives real source through parse, elaboration, lowering, and the scheduler
// with the driver's per-timestep recording loop installed, so the file-naming
// and port-selection rules are observed as the production task path applies
// them to arguments the parser actually produced.
class DumpportsSysTask : public VcdTestBase {
 protected:
  // Runs the source through the full pipeline with the driver's dump loop
  // (timestamp + changed values at the end of each time unit) and returns the
  // dump file contents. The fixture is caller-owned so its diagnostics and
  // context stay inspectable after the run.
  std::string RunVcd(SimFixture& f, const std::string& src) {
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      vcd.BeginScope("t");
      // Register in name order so identifier codes are deterministic: the
      // alphabetically first variable gets '!', the next '"', and so on.
      std::vector<std::pair<std::string_view, Variable*>> vars(
          f.ctx.GetVariables().begin(), f.ctx.GetVariables().end());
      std::sort(vars.begin(), vars.end(),
                [](const auto& a, const auto& b) { return a.first < b.first; });
      for (const auto& [name, var] : vars) {
        vcd.RegisterSignal(name, var->value.width, var);
      }
      vcd.EndScope();
      vcd.EndDefinitions();
      // Value change dumping starts only once the source's $dumpports call
      // schedules its opening checkpoint.
      vcd.ArmDumpvarsStart();
      f.ctx.SetVcdWriter(&vcd);
      f.scheduler.SetPostTimestepCallback([&vcd, &f]() {
        vcd.WriteTimestamp(f.ctx.CurrentTime().ticks);
        vcd.DumpChangedValues(0);
      });
      f.scheduler.Run();
    }  // writer destructor flushes the dump to tmp_path_ before ReadVcd
    return ReadVcd();
  }
};

// §21.7.3.1: with no arguments both $dumpports; and $dumpports(); are
// allowed, and the default values apply: the output file is dumpports.vcd and
// the scope is the calling module, so the module's objects are dumped.
TEST_F(DumpportsSysTask, NoArgumentFormsUseDefaults) {
  SimFixture f1;
  RunVcd(f1,
         "module t;\n"
         "  logic a;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    $dumpports;\n"
         "  end\n"
         "endmodule\n");
  EXPECT_FALSE(f1.diag.HasErrors());
  EXPECT_EQ(f1.ctx.GetDumpFileName(), "dumpports.vcd");

  SimFixture f2;
  auto content = RunVcd(f2,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports();\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f2.diag.HasErrors());
  EXPECT_EQ(f2.ctx.GetDumpFileName(), "dumpports.vcd");
  EXPECT_NE(content.find("1!"), std::string::npos);  // a dumped by default
}

// §21.7.3.1: a null first argument stands for the absent scope_list, so a
// comma precedes the filename. The scope defaults to the calling module and
// the trailing string literal names the VCD file.
TEST_F(DumpportsSysTask, NullScopeCommaThenStringLiteralFilename) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic b;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    b = 1'b0;\n"
                        "    $dumpports(, \"dump2.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.GetDumpFileName(), "dump2.dump");
  EXPECT_NE(content.find("1!"), std::string::npos);   // a dumped
  EXPECT_NE(content.find("0\""), std::string::npos);  // b dumped
}

// §21.7.3.1: the filename may be an expression of string data type; the
// characters the variable holds at the call name the file.
TEST_F(DumpportsSysTask, FilenameFromStringTypedVariable) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  string fn;\n"
         "  initial begin\n"
         "    fn = \"sv.vcd\";\n"
         "    $dumpports(, fn);\n"
         "  end\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.GetDumpFileName(), "sv.vcd");
}

// §21.7.3.1: the filename may also be an integral variable containing a
// character string, decoded byte by byte into the name.
TEST_F(DumpportsSysTask, FilenameFromIntegralVariable) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [55:0] fn;\n"
         "  initial begin\n"
         "    fn = \"int.vcd\";\n"
         "    $dumpports(, fn);\n"
         "  end\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.GetDumpFileName(), "int.vcd");
}

// §21.7.3.1: the filename variable may get its characters from a declaration
// initializer rather than a procedural assignment; the name it holds when the
// task executes is the one used.
TEST_F(DumpportsSysTask, FilenameFromDeclarationInitializedVariable) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [55:0] fn = \"ini.vcd\";\n"
         "  initial $dumpports(, fn);\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.GetDumpFileName(), "ini.vcd");
}

// §21.7.3.1: the filename argument is an expression, so a parameter constant
// holding the character string is also accepted as the trailing argument.
// The name stays within four characters: string parameters longer than that
// hit an upstream §6.20 32-bit truncation defect outside this subclause.
TEST_F(DumpportsSysTask, FilenameFromParameterConstant) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  parameter string FN = \"p.vc\";\n"
         "  initial $dumpports(, FN);\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.GetDumpFileName(), "p.vc");
}

// §21.7.3.1: a localparam constant holding the character string is likewise
// accepted as the filename expression (kept within four characters for the
// same upstream §6.20 truncation limit as the parameter form).
TEST_F(DumpportsSysTask, FilenameFromLocalparamConstant) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  localparam string FN = \"l.vc\";\n"
         "  initial $dumpports(, FN);\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.GetDumpFileName(), "l.vc");
}

// §21.7.3.1: $dumpports names the extended VCD file itself. In source that
// also carries a $dumpfile call ($21.7.1.1 syntax), the name in effect after
// the $dumpports call is the one that call supplied, not the 4-state task's.
TEST_F(DumpportsSysTask, NamesFileIndependentlyOfDumpfileCall) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    $dumpfile(\"dump1.dump\");\n"
         "    $dumpports(, \"dump2.dump\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.GetDumpFileName(), "dump2.dump");
}

// §21.7.3.1: the simulator carries out the file-writing checks for the named
// dump file. A filename pointing into a directory that does not exist cannot
// be written and is reported as an error; a writable name raises none (the
// accept path is held by the other filename tests).
TEST_F(DumpportsSysTask, UnwritablePathReportedAsError) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    $dumpports(, \"no_such_dir_21731/f.vcd\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
}

// §21.7.3.1: an already-existing file is silently overwritten. With stale
// bytes pre-placed in the output file, the run raises no error and leaves a
// freshly written dump with no trace of the old contents.
TEST_F(DumpportsSysTask, ExistingFileSilentlyOverwritten) {
  {
    std::ofstream stale(tmp_path_);
    stale << "STALE-CONTENT\n";
  }
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"dump2.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("STALE-CONTENT"), std::string::npos);
  EXPECT_NE(content.find("$date"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

// §21.7.3.1: ports that exist in instantiations below the scope_list are not
// dumped -- neither in the opening checkpoint nor as later value changes --
// while the listed module's own port keeps recording.
TEST_F(DumpportsSysTask, PortsBelowListedScopeNotDumped) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module leafA;\n"
                        "  logic [7:0] deep;\n"
                        "  initial begin\n"
                        "    deep = 8'h3C;\n"
                        "    #5 deep = 8'hFF;\n"
                        "  end\n"
                        "endmodule\n"
                        "module midA;\n"
                        "  logic [7:0] own;\n"
                        "  leafA g1();\n"
                        "  initial begin\n"
                        "    own = 8'hA5;\n"
                        "    #5 own = 8'h0F;\n"
                        "  end\n"
                        "endmodule\n"
                        "module t;\n"
                        "  midA c1();\n"
                        "  initial #1 $dumpports(c1, \"dump2.dump\");\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  // Sorted registration: c1.g1.deep -> '!', c1.own -> '"'.
  EXPECT_NE(content.find("b10100101 "), std::string::npos);  // own checkpoint
  EXPECT_NE(content.find("b1111 \""), std::string::npos);    // own change at #5
  EXPECT_EQ(content.find("b111100 "), std::string::npos);    // deep checkpoint
  EXPECT_EQ(content.find("b11111111"), std::string::npos);   // deep change
}

// §21.7.3.1: a path name using the period hierarchy separator may name a
// module deeper in the hierarchy; that module's own ports are dumped and the
// intermediate module's ports are not selected by it.
TEST_F(DumpportsSysTask, HierarchicalPathNamesModuleScope) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module leafA;\n"
                        "  logic [7:0] deep;\n"
                        "  initial deep = 8'h3C;\n"
                        "endmodule\n"
                        "module midA;\n"
                        "  logic [7:0] own;\n"
                        "  leafA g1();\n"
                        "  initial own = 8'hA5;\n"
                        "endmodule\n"
                        "module t;\n"
                        "  midA c1();\n"
                        "  initial $dumpports(c1.g1, \"dump2.dump\");\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("b111100 "), std::string::npos);    // c1.g1.deep
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);  // c1.own not
}

// §21.7.3.1: more than one module_identifier may appear in the scope_list,
// separated by commas; each listed module is dumped and an unlisted one is
// not.
TEST_F(DumpportsSysTask, MultipleScopeListModulesDumped) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module ma;\n"
                        "  logic [7:0] xa;\n"
                        "  initial xa = 8'h11;\n"
                        "endmodule\n"
                        "module mb;\n"
                        "  logic [7:0] xb;\n"
                        "  initial xb = 8'h22;\n"
                        "endmodule\n"
                        "module mc;\n"
                        "  logic [7:0] xc;\n"
                        "  initial xc = 8'h33;\n"
                        "endmodule\n"
                        "module t;\n"
                        "  ma c1();\n"
                        "  mb c2();\n"
                        "  mc c3();\n"
                        "  initial $dumpports(c1, c2, \"dump2.dump\");\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("b10001 "), std::string::npos);   // c1.xa dumped
  EXPECT_NE(content.find("b100010 "), std::string::npos);  // c2.xb dumped
  EXPECT_EQ(content.find("b110011"), std::string::npos);   // c3.xc excluded
}

// §21.7.3.1: when arguments are present but none is a trailing filename, the
// name still defaults to dumpports.vcd while the listed scope is dumped.
TEST_F(DumpportsSysTask, ScopeWithoutFilenameKeepsDefaultName) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module midA;\n"
                        "  logic [7:0] own;\n"
                        "  initial own = 8'hA5;\n"
                        "endmodule\n"
                        "module t;\n"
                        "  midA c1();\n"
                        "  initial $dumpports(c1);\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.GetDumpFileName(), "dumpports.vcd");
  EXPECT_NE(content.find("b10100101 "), std::string::npos);  // c1.own dumped
}

// §21.7.3.1: string literals are not allowed for a module_identifier, so a
// quoted name in a scope position is reported as an error.
TEST_F(DumpportsSysTask, StringLiteralScopeRejected) {
  SimFixture f;
  RunVcd(f,
         "module midA;\n"
         "  logic [7:0] own;\n"
         "  initial own = 8'hA5;\n"
         "endmodule\n"
         "module t;\n"
         "  midA c1();\n"
         "  initial $dumpports(\"c1\", \"dump2.dump\");\n"
         "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
}

// §21.7.3.1: only modules are allowed in the scope_list, not variables; an
// entry naming a variable of the design is reported as an error.
TEST_F(DumpportsSysTask, VariableScopeRejected) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [7:0] v;\n"
         "  initial begin\n"
         "    v = 8'h01;\n"
         "    $dumpports(v, \"dump2.dump\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
}

// §21.7.3.1: each scope in one call's scope_list shall be unique; the same
// module named twice in one call is reported as an error.
TEST_F(DumpportsSysTask, DuplicateScopeWithinCallRejected) {
  SimFixture f;
  RunVcd(f,
         "module midA;\n"
         "  logic [7:0] own;\n"
         "  initial own = 8'hA5;\n"
         "endmodule\n"
         "module t;\n"
         "  midA c1();\n"
         "  initial $dumpports(c1, c1, \"dump2.dump\");\n"
         "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
}

// §21.7.3.1: scope uniqueness spans separate $dumpports calls; a scope named
// by an earlier call may not be named again by a later one.
TEST_F(DumpportsSysTask, DuplicateScopeAcrossCallsRejected) {
  SimFixture f;
  RunVcd(f,
         "module midA;\n"
         "  logic [7:0] own;\n"
         "  initial own = 8'hA5;\n"
         "endmodule\n"
         "module t;\n"
         "  midA c1();\n"
         "  initial begin\n"
         "    $dumpports(c1, \"f1.vcd\");\n"
         "    $dumpports(c1, \"f2.vcd\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
}

// §21.7.3.1: specifying the same filename in more than one $dumpports call is
// not allowed, even when the scopes differ.
TEST_F(DumpportsSysTask, RepeatedFileNameAcrossCallsRejected) {
  SimFixture f;
  RunVcd(f,
         "module ma;\n"
         "  logic [7:0] xa;\n"
         "  initial xa = 8'h11;\n"
         "endmodule\n"
         "module mb;\n"
         "  logic [7:0] xb;\n"
         "  initial xb = 8'h22;\n"
         "endmodule\n"
         "module t;\n"
         "  ma c1();\n"
         "  mb c2();\n"
         "  initial begin\n"
         "    $dumpports(c1, \"same.vcd\");\n"
         "    $dumpports(c2, \"same.vcd\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
}

// §21.7.3.1: $dumpports can be invoked multiple times throughout the model
// when every execution is at the same simulation time; each call adds its
// scope to the dump.
TEST_F(DumpportsSysTask, MultipleCallsAtSameTimeAllowed) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module ma;\n"
                        "  logic [7:0] xa;\n"
                        "  initial xa = 8'h11;\n"
                        "endmodule\n"
                        "module mb;\n"
                        "  logic [7:0] xb;\n"
                        "  initial xb = 8'h22;\n"
                        "endmodule\n"
                        "module mc;\n"
                        "  logic [7:0] xc;\n"
                        "  initial xc = 8'h33;\n"
                        "endmodule\n"
                        "module t;\n"
                        "  ma c1();\n"
                        "  mb c2();\n"
                        "  mc c3();\n"
                        "  initial begin\n"
                        "    $dumpports(c1, \"f1.vcd\");\n"
                        "    $dumpports(c2, \"f2.vcd\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("b10001 "), std::string::npos);   // c1.xa dumped
  EXPECT_NE(content.find("b100010 "), std::string::npos);  // c2.xb dumped
  EXPECT_EQ(content.find("b110011"), std::string::npos);   // c3.xc excluded
}

// §21.7.3.1: the execution of all $dumpports tasks shall be at the same
// simulation time; a call at a later time is reported as an error.
TEST_F(DumpportsSysTask, CallsAtDifferentTimesRejected) {
  SimFixture f;
  RunVcd(f,
         "module ma;\n"
         "  logic [7:0] xa;\n"
         "  initial xa = 8'h11;\n"
         "endmodule\n"
         "module mb;\n"
         "  logic [7:0] xb;\n"
         "  initial xb = 8'h22;\n"
         "endmodule\n"
         "module t;\n"
         "  ma c1();\n"
         "  mb c2();\n"
         "  initial begin\n"
         "    $dumpports(c1, \"f1.vcd\");\n"
         "    #10 $dumpports(c2, \"f2.vcd\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
}

// §21.7.3.1: when $dumpports executes, the associated value change dumping
// starts at the end of the current simulation time unit: a value assigned
// after the call but within the same time unit is what the opening checkpoint
// records, and the value the variable held at the execution point never
// reaches the file.
TEST_F(DumpportsSysTask, DumpingStartsAtEndOfCurrentTimeUnit) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b0;\n"
                        "    $dumpports(, \"dump2.dump\");\n"
                        "    a = 1'b1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("1!"), std::string::npos);  // end-of-unit value
  EXPECT_EQ(content.find("0!"), std::string::npos);  // call-point value absent
}

// §21.7.3.1: the end-of-time-unit start holds mid-simulation too: executed at
// a nonzero time, the opening checkpoint is stamped with that time and
// records the value assigned after the call within the same time unit.
TEST_F(DumpportsSysTask, EndOfUnitStartAtNonzeroExecutionTime) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b0;\n"
                        "    #7 $dumpports(, \"dump2.dump\");\n"
                        "    a = 1'b1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("#7"), std::string::npos);  // checkpoint's time unit
  EXPECT_NE(content.find("1!"), std::string::npos);  // end-of-unit value
  EXPECT_EQ(content.find("0!"), std::string::npos);  // call-point value absent
}

// §21.7.3.1: the end-of-time-unit start also picks up a value produced by a
// nonblocking assignment in the same time unit -- NBA updates land before the
// unit ends, so the opening checkpoint records the updated value, not the one
// held when the task executed.
TEST_F(DumpportsSysTask, EndOfUnitCheckpointSeesNonblockingUpdate) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b0;\n"
                        "    $dumpports(, \"dump2.dump\");\n"
                        "    a <= 1'b1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("1!"), std::string::npos);  // NBA-updated value
  EXPECT_EQ(content.find("0!"), std::string::npos);  // pre-update value absent
}

// §21.7.3.1: $dumpports can be used in source code that also contains the
// $dumpvars task; both start their dumps (each with its own checkpoint
// section) and later changes keep recording, with no error raised.
TEST_F(DumpportsSysTask, CoexistsWithDumpvarsInSameSource) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b0;\n"
                        "    $dumpvars;\n"
                        "    $dumpports(, \"dump2.dump\");\n"
                        "    #10 a = 1'b1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto first = content.find("$dumpvars");
  ASSERT_NE(first, std::string::npos);
  EXPECT_NE(content.rfind("$dumpvars"), first);  // one section per task
  EXPECT_NE(content.find("#10"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);  // recording continues
}

}  // namespace
}  // namespace delta
