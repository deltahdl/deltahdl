#include <gtest/gtest.h>

#include <cctype>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
#include "helpers_vcd_var_decl.h"

namespace delta {
namespace {

class VcdTypeMappingSim : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src, const std::string& scope = "t") {
    return RunVcdDump(
        src, {.scope = scope,
              .registration = VcdSignalRegistration::kContextFiltered});
  }
};

std::vector<std::string> RealChanges(const std::string& content,
                                     std::string_view ident) {
  std::vector<std::string> out;
  for (const auto& l : AllLines(content)) {
    auto toks = Tokens(l);
    if (toks.size() == 2 && toks[1] == ident && toks[0].size() > 1 &&
        toks[0][0] == 'r') {
      out.push_back(toks[0].substr(1));
    }
  }
  return out;
}

TEST_F(VcdTypeMappingSim, FixedWidthIntegerTypesMapPerTable) {
  auto content = RunVcd(
      "module t;\n"
      "  int wi;\n"
      "  shortint ws;\n"
      "  longint wl;\n"
      "  byte wb;\n"
      "  initial begin\n"
      "    wi = 0; ws = 0; wl = 0; wb = 0;\n"
      "    $dumpvars;\n"
      "    #1 wi = 1;\n"
      "  end\n"
      "endmodule\n");
  auto wi = VarDecl(content, "wi");
  ASSERT_EQ(wi.size(), 6u) << content;
  EXPECT_EQ(wi[1], "integer");
  EXPECT_EQ(wi[2], "32");

  auto ws = VarDecl(content, "ws");
  ASSERT_EQ(ws.size(), 6u) << content;
  EXPECT_EQ(ws[1], "reg");
  EXPECT_EQ(ws[2], "16");

  auto wl = VarDecl(content, "wl");
  ASSERT_EQ(wl.size(), 6u) << content;
  EXPECT_EQ(wl[1], "reg");
  EXPECT_EQ(wl[2], "64");

  auto wb = VarDecl(content, "wb");
  ASSERT_EQ(wb.size(), 6u) << content;
  EXPECT_EQ(wb[1], "reg");
  EXPECT_EQ(wb[2], "8");

  EXPECT_NE(wi[1], "reg");
  EXPECT_NE(wi[1], "wire");
}

TEST_F(VcdTypeMappingSim, BitMasqueradesAsRegAndPackedArrayCollapses) {
  auto content = RunVcd(
      "module t;\n"
      "  bit [3:0] flags;\n"
      "  bit [3:0][7:0] word;\n"
      "  initial begin\n"
      "    flags = 0; word = 0;\n"
      "    $dumpvars;\n"
      "    #1 flags = 4'hA;\n"
      "  end\n"
      "endmodule\n");
  auto flags = VarDecl(content, "flags");
  ASSERT_EQ(flags.size(), 6u) << content;
  EXPECT_EQ(flags[1], "reg");
  EXPECT_EQ(flags[2], "4");

  auto word = VarDecl(content, "word");
  ASSERT_EQ(word.size(), 6u) << content;
  EXPECT_EQ(word[1], "reg");
  EXPECT_EQ(word[2], "32");

  EXPECT_NE(flags[1], "wire");
}

TEST_F(VcdTypeMappingSim, UntypedEnumMapsToIntegerThirtyTwo) {
  auto content = RunVcd(
      "module t;\n"
      "  enum {RED, GREEN, BLUE} e;\n"
      "  initial begin\n"
      "    e = GREEN;\n"
      "    $dumpvars;\n"
      "    #1 e = BLUE;\n"
      "  end\n"
      "endmodule\n");
  auto e = VarDecl(content, "e");
  ASSERT_EQ(e.size(), 6u) << content;
  EXPECT_EQ(e[1], "integer");
  EXPECT_EQ(e[2], "32");
}

TEST_F(VcdTypeMappingSim, TypedEnumDumpsAsSpecifiedBaseType) {
  auto content = RunVcd(
      "module t;\n"
      "  enum bit [3:0] {A, B, C} e;\n"
      "  initial begin\n"
      "    e = B;\n"
      "    $dumpvars;\n"
      "    #1 e = C;\n"
      "  end\n"
      "endmodule\n");
  auto e = VarDecl(content, "e");
  ASSERT_EQ(e.size(), 6u) << content;
  EXPECT_EQ(e[1], "reg");
  EXPECT_EQ(e[2], "4");
  EXPECT_NE(e[1], "integer");
  EXPECT_NE(e[2], "32");
}

TEST_F(VcdTypeMappingSim, TypedefEnumFollowsResolvedType) {
  auto content = RunVcd(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  typedef enum bit [3:0] {A, B, C} nibble_t;\n"
      "  color_t c;\n"
      "  nibble_t n;\n"
      "  initial begin\n"
      "    c = GREEN; n = B;\n"
      "    $dumpvars;\n"
      "    #1 c = BLUE;\n"
      "  end\n"
      "endmodule\n");
  auto c = VarDecl(content, "c");
  ASSERT_EQ(c.size(), 6u) << content;
  EXPECT_EQ(c[1], "integer");
  EXPECT_EQ(c[2], "32");

  auto n = VarDecl(content, "n");
  ASSERT_EQ(n.size(), 6u) << content;
  EXPECT_EQ(n[1], "reg");
  EXPECT_EQ(n[2], "4");
  EXPECT_NE(n[1], "wire");
  EXPECT_NE(n[1], "integer");
}

TEST_F(VcdTypeMappingSim, PackedStructDumpsAsSingleRegVector) {
  auto content = RunVcd(
      "module t;\n"
      "  struct packed { byte hi; bit [3:0] lo; } s;\n"
      "  initial begin\n"
      "    s = 0;\n"
      "    $dumpvars;\n"
      "    #1 s.lo = 4'h5;\n"
      "  end\n"
      "endmodule\n");
  auto s = VarDecl(content, "s");
  ASSERT_EQ(s.size(), 6u) << content;
  EXPECT_EQ(s[1], "reg");
  EXPECT_EQ(s[2], "12");
  EXPECT_NE(s[1], "wire");
}

TEST_F(VcdTypeMappingSim, ShortrealMasqueradesAsReal) {
  auto content = RunVcd(
      "module t;\n"
      "  shortreal sr;\n"
      "  initial begin\n"
      "    sr = 1.5;\n"
      "    $dumpvars;\n"
      "    #1 sr = 3.5;\n"
      "  end\n"
      "endmodule\n");
  auto sr = VarDecl(content, "sr");
  ASSERT_EQ(sr.size(), 6u) << content;
  EXPECT_EQ(sr[1], "real");
  EXPECT_EQ(sr[2], "32");

  EXPECT_NE(sr[1], "reg");
  EXPECT_NE(sr[1], "integer");
  EXPECT_NE(sr[1], "wire");
}

TEST_F(VcdTypeMappingSim, ShortrealDumpsItsValue) {
  auto content = RunVcd(
      "module t;\n"
      "  shortreal sr;\n"
      "  initial begin\n"
      "    sr = 1.5;\n"
      "    $dumpvars;\n"
      "    #1 sr = 3.5;\n"
      "  end\n"
      "endmodule\n");
  auto sr = VarDecl(content, "sr");
  ASSERT_EQ(sr.size(), 6u) << content;
  auto changes = RealChanges(content, sr[3]);
  ASSERT_EQ(changes.size(), 2u) << content;
  EXPECT_EQ(changes[0], "1.5");
  EXPECT_EQ(changes[1], "3.5");
}

TEST_F(VcdTypeMappingSim, UnpackedArrayAndAutomaticVariablesNotDumped) {
  auto content = RunVcd(
      "module t;\n"
      "  int scalar_v;\n"
      "  int mem [0:3];\n"
      "  function automatic int f(int x);\n"
      "    int local_tmp;\n"
      "    local_tmp = x + 1;\n"
      "    return local_tmp;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    scalar_v = f(6);\n"
      "    mem[0] = 8'hAA;\n"
      "    $dumpvars;\n"
      "    #1 scalar_v = 9;\n"
      "  end\n"
      "endmodule\n");
  auto scalar_v = VarDecl(content, "scalar_v");
  ASSERT_EQ(scalar_v.size(), 6u) << content;
  EXPECT_EQ(scalar_v[1], "integer");

  EXPECT_FALSE(HasVar(content, "mem"));
  for (const auto& l : AllLines(content)) {
    EXPECT_EQ(l.find(" mem"), std::string::npos) << "array reached dump: " << l;
  }
  EXPECT_FALSE(HasVar(content, "local_tmp"));
}

const char kStringBesideIntTop[] =
    "module t;\n"
    "  string s;\n"
    "  int scalar_v;\n"
    "  initial begin\n"
    "    scalar_v = 5;\n"
    "    $dumpvars;\n"
    "    #1 scalar_v = 9;\n"
    "  end\n"
    "endmodule\n";

TEST_F(VcdTypeMappingSim, StringVariableIsNotDumped) {
  auto content = RunVcd(kStringBesideIntTop);
  auto scalar_v = VarDecl(content, "scalar_v");
  ASSERT_EQ(scalar_v.size(), 6u) << content;
  EXPECT_EQ(scalar_v[1], "integer");
  EXPECT_EQ(scalar_v[2], "32");

  EXPECT_FALSE(HasVar(content, "s")) << content;
}

bool IsBaselessValueChange(const std::string& line) {
  if (line.empty()) return false;
  char base = line[0];
  if (base != 'b' && base != 'B' && base != 'r' && base != 'R') return false;
  return line.size() == 1 ||
         std::isspace(static_cast<unsigned char>(line[1])) != 0;
}

TEST_F(VcdTypeMappingSim, StringContributesNoBaselessValueChange) {
  auto content = RunVcd(kStringBesideIntTop);
  auto scalar_v = VarDecl(content, "scalar_v");
  ASSERT_EQ(scalar_v.size(), 6u) << content;

  for (const auto& l : AllLines(content)) {
    EXPECT_FALSE(IsBaselessValueChange(l))
        << "base letter with no value digits: " << l << "\n"
        << content;
  }
}

TEST_F(VcdTypeMappingSim, ScalarBitDumpsAsOneBitReg) {
  auto content = RunVcd(
      "module t;\n"
      "  bit flag;\n"
      "  initial begin\n"
      "    flag = 1'b0;\n"
      "    $dumpvars;\n"
      "    #1 flag = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto flag = VarDecl(content, "flag");
  ASSERT_EQ(flag.size(), 6u) << content;
  EXPECT_EQ(flag[1], "reg");
  EXPECT_EQ(flag[2], "1");
  EXPECT_NE(flag[1], "wire");
}

TEST_F(VcdTypeMappingSim, EnumWithByteBaseDumpsAsThatBase) {
  auto content = RunVcd(
      "module t;\n"
      "  enum byte {LOW, MID, HIGH} e;\n"
      "  initial begin\n"
      "    e = MID;\n"
      "    $dumpvars;\n"
      "    #1 e = HIGH;\n"
      "  end\n"
      "endmodule\n");
  auto e = VarDecl(content, "e");
  ASSERT_EQ(e.size(), 6u) << content;
  EXPECT_EQ(e[1], "reg");
  EXPECT_EQ(e[2], "8");
  EXPECT_NE(e[1], "integer");
  EXPECT_NE(e[2], "32");
}

TEST_F(VcdTypeMappingSim, TypedefPackedStructDumpsAsRegVector) {
  auto content = RunVcd(
      "module t;\n"
      "  typedef struct packed { byte hi; bit [3:0] lo; } word_t;\n"
      "  word_t s;\n"
      "  initial begin\n"
      "    s = 0;\n"
      "    $dumpvars;\n"
      "    #1 s.lo = 4'h5;\n"
      "  end\n"
      "endmodule\n");
  auto s = VarDecl(content, "s");
  ASSERT_EQ(s.size(), 6u) << content;
  EXPECT_EQ(s[1], "reg");
  EXPECT_EQ(s[2], "12");
  EXPECT_NE(s[1], "wire");
}

TEST_F(VcdTypeMappingSim, DeclarationInitializerKeepsTypeMapping) {
  auto content = RunVcd(
      "module t;\n"
      "  int wi = 7;\n"
      "  byte wb = 8'h5;\n"
      "  bit [3:0] wv = 4'hC;\n"
      "  initial begin\n"
      "    $dumpvars;\n"
      "    #1 wi = 8;\n"
      "  end\n"
      "endmodule\n");
  auto wi = VarDecl(content, "wi");
  ASSERT_EQ(wi.size(), 6u) << content;
  EXPECT_EQ(wi[1], "integer");
  EXPECT_EQ(wi[2], "32");

  auto wb = VarDecl(content, "wb");
  ASSERT_EQ(wb.size(), 6u) << content;
  EXPECT_EQ(wb[1], "reg");
  EXPECT_EQ(wb[2], "8");

  auto wv = VarDecl(content, "wv");
  ASSERT_EQ(wv.size(), 6u) << content;
  EXPECT_EQ(wv[1], "reg");
  EXPECT_EQ(wv[2], "4");
}

TEST_F(VcdTypeMappingSim, PortDeclarationsMapPerTable) {
  auto content = RunVcd(
      "module t(output int po, output byte pb);\n"
      "  initial begin\n"
      "    po = 0; pb = 0;\n"
      "    $dumpvars;\n"
      "    #1 po = 1;\n"
      "  end\n"
      "endmodule\n");
  auto po = VarDecl(content, "po");
  ASSERT_EQ(po.size(), 6u) << content;
  EXPECT_EQ(po[1], "integer");
  EXPECT_EQ(po[2], "32");

  auto pb = VarDecl(content, "pb");
  ASSERT_EQ(pb.size(), 6u) << content;
  EXPECT_EQ(pb[1], "reg");
  EXPECT_EQ(pb[2], "8");
}

const char kBytePortLeaf[] =
    "module leaf(output byte pb);\n"
    "  initial begin\n"
    "    pb = 0;\n"
    "    $dumpvars;\n"
    "    #1 pb = 8'h5;\n"
    "  end\n"
    "endmodule\n";

std::string BytePortLeafInstantiated() {
  return std::string(kBytePortLeaf) +
         "module t;\n"
         "  byte w;\n"
         "  leaf u (.pb(w));\n"
         "endmodule\n";
}

TEST_F(VcdTypeMappingSim, ChildInstancePortMapsPerTable) {
  auto content = RunVcd(BytePortLeafInstantiated());
  auto pb = VarDecl(content, "pb");
  ASSERT_EQ(pb.size(), 6u) << content;
  EXPECT_EQ(pb[1], "reg");
  EXPECT_EQ(pb[2], "8");

  EXPECT_NE(pb[1], "wire");
}

TEST_F(VcdTypeMappingSim, TopAndChildInstancePortsOfOneModuleDumpAlike) {
  auto top_content = RunVcd(kBytePortLeaf, "leaf");
  auto child_content = RunVcd(BytePortLeafInstantiated());
  auto top_pb = VarDecl(top_content, "pb");
  auto child_pb = VarDecl(child_content, "pb");
  ASSERT_EQ(top_pb.size(), 6u) << top_content;
  ASSERT_EQ(child_pb.size(), 6u) << child_content;

  EXPECT_EQ(child_pb[1], top_pb[1]);
  EXPECT_EQ(child_pb[2], top_pb[2]);
}

const char kBodyVarLeaf[] =
    "module leaf;\n"
    "  byte b;\n"
    "  real r;\n"
    "  string s;\n"
    "  event ev;\n"
    "  initial begin\n"
    "    b = 0;\n"
    "    $dumpvars;\n"
    "    #1 b = 8'h5;\n"
    "  end\n"
    "endmodule\n";

std::string BodyVarLeafInstantiated() {
  return std::string(kBodyVarLeaf) +
         "module t;\n"
         "  leaf u ();\n"
         "endmodule\n";
}

TEST_F(VcdTypeMappingSim, TopAndChildInstanceBodyByteDumpsAlike) {
  auto top_content = RunVcd(kBodyVarLeaf, "leaf");
  auto child_content = RunVcd(BodyVarLeafInstantiated());
  auto top_b = VarDecl(top_content, "b");
  auto child_b = VarDecl(child_content, "b");
  ASSERT_EQ(top_b.size(), 6u) << top_content;
  ASSERT_EQ(child_b.size(), 6u) << child_content;

  EXPECT_EQ(child_b[1], top_b[1]);
  EXPECT_EQ(child_b[2], top_b[2]);
}

TEST_F(VcdTypeMappingSim, TopAndChildInstanceBodyRealDumpsAlike) {
  auto top_content = RunVcd(kBodyVarLeaf, "leaf");
  auto child_content = RunVcd(BodyVarLeafInstantiated());
  auto top_r = VarDecl(top_content, "r");
  auto child_r = VarDecl(child_content, "r");
  ASSERT_EQ(top_r.size(), 6u) << top_content;
  ASSERT_EQ(child_r.size(), 6u) << child_content;

  EXPECT_EQ(child_r[1], top_r[1]);
  EXPECT_EQ(child_r[2], top_r[2]);
}

TEST_F(VcdTypeMappingSim, TopAndChildInstanceBodyEventDumpsAlike) {
  auto top_content = RunVcd(kBodyVarLeaf, "leaf");
  auto child_content = RunVcd(BodyVarLeafInstantiated());
  auto top_ev = VarDecl(top_content, "ev");
  auto child_ev = VarDecl(child_content, "ev");
  ASSERT_EQ(top_ev.size(), 6u) << top_content;
  ASSERT_EQ(child_ev.size(), 6u) << child_content;

  EXPECT_EQ(top_ev[1], "event");
  EXPECT_EQ(child_ev[1], "event");
}

TEST_F(VcdTypeMappingSim, ChildInstanceBodyStringIsNotDumped) {
  auto child_content = RunVcd(BodyVarLeafInstantiated());
  auto child_b = VarDecl(child_content, "b");
  ASSERT_EQ(child_b.size(), 6u) << child_content;

  EXPECT_FALSE(HasVar(child_content, "s")) << child_content;
}

TEST_F(VcdTypeMappingSim, MappedDeclarationsSitInsideModuleScopeSection) {
  auto content = RunVcd(
      "module t;\n"
      "  int counter;\n"
      "  byte tag;\n"
      "  initial begin\n"
      "    counter = 0; tag = 0;\n"
      "    $dumpvars;\n"
      "    #1 counter = 1;\n"
      "  end\n"
      "endmodule\n");
  auto scope_pos = content.find("$scope module t $end");
  auto upscope_pos = content.find("$upscope $end");
  ASSERT_NE(scope_pos, std::string::npos) << content;
  ASSERT_NE(upscope_pos, std::string::npos) << content;

  auto counter_pos = content.find(" counter $end");
  auto tag_pos = content.find(" tag $end");
  ASSERT_NE(counter_pos, std::string::npos) << content;
  ASSERT_NE(tag_pos, std::string::npos) << content;
  EXPECT_GT(counter_pos, scope_pos);
  EXPECT_LT(counter_pos, upscope_pos);
  EXPECT_GT(tag_pos, scope_pos);
  EXPECT_LT(tag_pos, upscope_pos);

  auto counter_decl = VarDecl(content, "counter");
  ASSERT_EQ(counter_decl.size(), 6u) << content;
  EXPECT_EQ(counter_decl[1], "integer");
  auto tag_decl = VarDecl(content, "tag");
  ASSERT_EQ(tag_decl.size(), 6u) << content;
  EXPECT_EQ(tag_decl[1], "reg");
  EXPECT_EQ(tag_decl[2], "8");
}

TEST_F(VcdTypeMappingSim, UnpackedStructAppearsAsForkJoinBlock) {
  auto content = RunVcd(
      "module t;\n"
      "  struct { byte header; bit valid; int seq; } pkt;\n"
      "  initial begin\n"
      "    pkt.header = 8'h11; pkt.valid = 1'b0; pkt.seq = 0;\n"
      "    $dumpvars;\n"
      "    #1 pkt.valid = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$scope fork pkt $end"), std::string::npos) << content;
  EXPECT_EQ(content.find("$scope module pkt $end"), std::string::npos);
  EXPECT_FALSE(HasVar(content, "pkt"));

  auto header = VarDecl(content, "header");
  ASSERT_EQ(header.size(), 6u) << content;
  EXPECT_EQ(header[1], "reg");
  EXPECT_EQ(header[2], "8");

  auto valid = VarDecl(content, "valid");
  ASSERT_EQ(valid.size(), 6u) << content;
  EXPECT_EQ(valid[1], "reg");
  EXPECT_EQ(valid[2], "1");

  auto seq = VarDecl(content, "seq");
  ASSERT_EQ(seq.size(), 6u) << content;
  EXPECT_EQ(seq[1], "integer");
  EXPECT_EQ(seq[2], "32");

  auto fork_pos = content.find("$scope fork pkt $end");
  auto up_pos = content.find("$upscope $end", fork_pos);
  ASSERT_NE(up_pos, std::string::npos) << content;
  auto header_pos = content.find(" header $end");
  ASSERT_NE(header_pos, std::string::npos) << content;
  EXPECT_GT(header_pos, fork_pos);
  EXPECT_LT(header_pos, up_pos);
}

TEST_F(VcdTypeMappingSim, UnpackedStructMembersDumpTheirOwnValues) {
  auto content = RunVcd(
      "module t;\n"
      "  struct { byte header; bit valid; } pkt;\n"
      "  initial begin\n"
      "    pkt.header = 8'h00; pkt.valid = 1'b0;\n"
      "    $dumpvars;\n"
      "    #1 pkt.header = 8'h5A;\n"
      "  end\n"
      "endmodule\n");
  auto header = VarDecl(content, "header");
  auto valid = VarDecl(content, "valid");
  ASSERT_EQ(header.size(), 6u) << content;
  ASSERT_EQ(valid.size(), 6u) << content;
  EXPECT_NE(header[3], valid[3]);

  auto lines = AllLines(content);
  bool saw_header_change = false;
  for (const auto& l : lines) {
    if (l == "b1011010 " + header[3]) saw_header_change = true;
  }
  EXPECT_TRUE(saw_header_change) << content;
}

}  // namespace
}  // namespace delta
