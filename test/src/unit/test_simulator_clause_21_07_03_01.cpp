#include "builders_systask.h"
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Exercises the $dumpports system task end to end so the file-naming and
// port-selection rules of §21.7.3.1 are observed as the production task path
// applies them.
class DumpportsSysTask : public VcdTestBase {};

// §21.7.3.1: with no arguments ($dumpports; / $dumpports();) the default values
// for the arguments are used, so the output file is named dumpports.vcd in the
// working directory.
TEST_F(DumpportsSysTask, NoArgsDefaultsToDumpportsVcd) {
  SimFixture f;
  EvalExpr(MkSysCall(f.arena, "$dumpports", {}), f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetDumpFileName(), "dumpports.vcd");
}

// §21.7.3.1: the filename is the trailing argument and may be given as a string
// literal that denotes the VCD output file.
TEST_F(DumpportsSysTask, FilenameTakenFromTrailingStringLiteral) {
  SimFixture f;
  EvalExpr(MkSysCall(f.arena, "$dumpports",
                     {MkId(f.arena, "top"), MkStr(f.arena, "ports.vcd")}),
           f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetDumpFileName(), "ports.vcd");
}

// §21.7.3.1: when the first argument (scope_list) is null a leading comma
// precedes the filename, leaving the scope as the calling module. Every port
// registered from the point of the call is then a primary I/O pin and dumped.
TEST_F(DumpportsSysTask, IncludesRegisteredPortsWhenScopeOmitted) {
  SimFixture f;
  auto* a = MakeVar(f, "a", 1, 1);
  auto* b = MakeVar(f, "b", 1, 0);
  VcdWriter vcd(tmp_path_);
  vcd.WriteHeader("1ns");
  vcd.RegisterSignal("a", 1, a);  // ident '!'
  vcd.RegisterSignal("b", 1, b);  // ident '"'
  vcd.EndDefinitions();
  vcd.WriteTimestamp(0);
  f.ctx.SetVcdWriter(&vcd);

  // Null scope_list expressed with a leading comma before the filename; the
  // parser represents the absent first argument as a null argument expression.
  EvalExpr(
      MkSysCall(f.arena, "$dumpports", {nullptr, MkStr(f.arena, "ports.vcd")}),
      f.ctx, f.arena);

  auto content = ReadVcd();
  EXPECT_NE(content.find("1!"), std::string::npos);  // a dumped
  EXPECT_NE(content.find("0\""), std::string::npos);  // b dumped
}

// §21.7.3.1: when a scope_list is given, the ports in those scopes are dumped
// and ports outside them are not.
TEST_F(DumpportsSysTask, DumpsOnlyNamedScope) {
  SimFixture f;
  auto* a = MakeVar(f, "a", 1, 1);
  auto* b = MakeVar(f, "b", 1, 0);
  VcdWriter vcd(tmp_path_);
  vcd.WriteHeader("1ns");
  vcd.RegisterSignal("a", 1, a);  // ident '!'
  vcd.RegisterSignal("b", 1, b);  // ident '"'
  vcd.EndDefinitions();
  vcd.WriteTimestamp(0);
  f.ctx.SetVcdWriter(&vcd);

  EvalExpr(MkSysCall(f.arena, "$dumpports",
                     {MkId(f.arena, "a"), MkStr(f.arena, "ports.vcd")}),
           f.ctx, f.arena);

  auto content = ReadVcd();
  EXPECT_NE(content.find("1!"), std::string::npos);   // a dumped
  EXPECT_EQ(content.find("0\""), std::string::npos);  // b not dumped
}

// §21.7.3.1: a scope_list may name more than one module, separated by commas.
// Every named scope is dumped and a scope not listed is excluded.
TEST_F(DumpportsSysTask, DumpsMultipleNamedScopes) {
  SimFixture f;
  auto* a = MakeVar(f, "a", 1, 1);
  auto* b = MakeVar(f, "b", 1, 1);
  auto* c = MakeVar(f, "c", 1, 0);
  VcdWriter vcd(tmp_path_);
  vcd.WriteHeader("1ns");
  vcd.RegisterSignal("a", 1, a);  // ident '!'
  vcd.RegisterSignal("b", 1, b);  // ident '"'
  vcd.RegisterSignal("c", 1, c);  // ident '#'
  vcd.EndDefinitions();
  vcd.WriteTimestamp(0);
  f.ctx.SetVcdWriter(&vcd);

  EvalExpr(MkSysCall(f.arena, "$dumpports",
                     {MkId(f.arena, "a"), MkId(f.arena, "b"),
                      MkStr(f.arena, "ports.vcd")}),
           f.ctx, f.arena);

  auto content = ReadVcd();
  EXPECT_NE(content.find("1!"), std::string::npos);   // a dumped
  EXPECT_NE(content.find("1\""), std::string::npos);  // b dumped
  EXPECT_EQ(content.find("0#"), std::string::npos);   // c not dumped
}

// §21.7.3.1: a scope may be given as a hierarchical path using the period
// separator; it resolves to the named scope whose ports are dumped.
TEST_F(DumpportsSysTask, ResolvesHierarchicalScopeName) {
  SimFixture f;
  auto* sig = MakeVar(f, "sig", 1, 1);
  auto* other = MakeVar(f, "other", 1, 0);
  VcdWriter vcd(tmp_path_);
  vcd.WriteHeader("1ns");
  vcd.RegisterSignal("sig", 1, sig);      // ident '!'
  vcd.RegisterSignal("other", 1, other);  // ident '"'
  vcd.EndDefinitions();
  vcd.WriteTimestamp(0);
  f.ctx.SetVcdWriter(&vcd);

  EvalExpr(MkSysCall(f.arena, "$dumpports",
                     {MkId(f.arena, "top.sig"), MkStr(f.arena, "ports.vcd")}),
           f.ctx, f.arena);

  auto content = ReadVcd();
  EXPECT_NE(content.find("1!"), std::string::npos);   // top.sig -> sig dumped
  EXPECT_EQ(content.find("0\""), std::string::npos);  // other not dumped
}

// §21.7.3.1: when arguments are present but none is a trailing filename literal,
// the filename still defaults to dumpports.vcd while the scope is dumped.
TEST_F(DumpportsSysTask, ScopeWithoutFilenameDefaultsName) {
  SimFixture f;
  auto* sig = MakeVar(f, "sig", 1, 1);
  VcdWriter vcd(tmp_path_);
  vcd.WriteHeader("1ns");
  vcd.RegisterSignal("sig", 1, sig);  // ident '!'
  vcd.EndDefinitions();
  vcd.WriteTimestamp(0);
  f.ctx.SetVcdWriter(&vcd);

  EvalExpr(MkSysCall(f.arena, "$dumpports", {MkId(f.arena, "sig")}), f.ctx,
           f.arena);

  EXPECT_EQ(f.ctx.GetDumpFileName(), "dumpports.vcd");
  EXPECT_NE(ReadVcd().find("1!"), std::string::npos);  // sig dumped
}

// §21.7.3.1: a string literal is not allowed as a scope_list entry (a scope
// names a module). Supplying one in a scope position is reported as an error,
// while the trailing string literal naming the file remains valid.
TEST_F(DumpportsSysTask, RejectsStringLiteralScope) {
  SimFixture f;
  auto* sig = MakeVar(f, "sig", 1, 1);
  VcdWriter vcd(tmp_path_);
  vcd.WriteHeader("1ns");
  vcd.RegisterSignal("sig", 1, sig);
  vcd.EndDefinitions();
  vcd.WriteTimestamp(0);
  f.ctx.SetVcdWriter(&vcd);

  EvalExpr(MkSysCall(f.arena, "$dumpports",
                     {MkStr(f.arena, "top"), MkStr(f.arena, "ports.vcd")}),
           f.ctx, f.arena);

  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
}  // namespace delta
