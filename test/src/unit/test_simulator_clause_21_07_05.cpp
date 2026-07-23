#include <string>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor is
// well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.5 ("VCD SystemVerilog type mappings"): SystemVerilog does not extend
// the IEEE Std 1364-2005 VCD format, so a SystemVerilog data type is dumped by
// masquerading as a 1364-2005 type. Table 21-11 fixes the var_type keyword and
// size each basic type is dumped with, and the surrounding prose adds four
// rules: a packed array or structure collapses to a single reg vector; a typed
// enum is dumped as its base type rather than the default integer/32; an
// unpacked structure appears as a named fork-join block whose members are
// dumped as their mapped types; and unpacked arrays and automatic variables are
// not dumped.
//
// The keyword and size chosen for a $var declaration depend on how the object
// was declared in the source, so these rules are exercised by driving real
// SystemVerilog through the full pipeline (parse, elaborate, lower, register)
// and reading the $var declarations the writer produced. Two facets are covered
// at the writer stage directly, and each is documented at its test: a 4-state
// logic variable's registration is fixed to the net var_type default by
// §21.7.2.1 (whose e2e dumps pin `logic` -> wire), so only the writer's mapping
// of a logic-typed object to reg is observable here; and an unpacked structure
// reaches the writer as one flat object with no per-field sub-objects, so the
// fork-join scope form is exercised through the writer's scope API.
class VcdTypeMappingSim : public VcdTestBase {
 protected:
  // Runs a single-module source through the full pipeline with the driver's
  // registration sequence (header, module scope, one registration per model
  // variable via RegisterVcdSignals, $enddefinitions) and returns the dump file
  // contents. Identifier codes ascend from '!' in variable-name order.
  std::string RunVcd(const std::string& src, const std::string& scope = "t") {
    SimFixture f;
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      vcd.BeginScope(scope);
      f.ctx.RegisterVcdSignals(vcd);
      vcd.EndScope();
      vcd.EndDefinitions();
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

std::vector<std::string> Lines(const std::string& content) {
  std::vector<std::string> out;
  std::string cur;
  for (char c : content) {
    if (c == '\n') {
      out.push_back(cur);
      cur.clear();
    } else {
      cur.push_back(c);
    }
  }
  if (!cur.empty()) out.push_back(cur);
  return out;
}

std::vector<std::string> Tokens(const std::string& line) {
  std::vector<std::string> out;
  std::string cur;
  for (char c : line) {
    if (c == ' ') {
      if (!cur.empty()) out.push_back(cur);
      cur.clear();
    } else {
      cur.push_back(c);
    }
  }
  if (!cur.empty()) out.push_back(cur);
  return out;
}

// Tokens of the $var declaration whose reference name is `name`
// ($var var_type size identifier_code reference $end), or empty when absent.
// Robust to the identifier code, which depends on registration order.
std::vector<std::string> VarDecl(const std::string& content,
                                 std::string_view name) {
  for (const auto& l : Lines(content)) {
    auto toks = Tokens(l);
    if (toks.size() == 6 && toks[0] == "$var" && toks[4] == name) return toks;
  }
  return {};
}

// True when any $var declaration in the dump names `name`.
bool HasVar(const std::string& content, std::string_view name) {
  return !VarDecl(content, name).empty();
}

// ---------------------------------------------------------------------------
// Table 21-11: the fixed-width integer types masquerade as their tabulated
// 1364-2005 type and size. int -> integer/32, shortint -> reg/16,
// longint -> reg/64, byte -> reg/8. The keyword distinguishes int (integer)
// from the reg-mapped types, and the size is fixed by the table. The negative
// each rule must avoid is the pre-existing net default: none of these carries
// the wire keyword the net form (§21.7.2.3) would give an unmapped object.
// ---------------------------------------------------------------------------
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

  // Negative: an int masquerades as integer, never as the reg the other
  // integer types use nor the wire an unmapped object would default to.
  EXPECT_NE(wi[1], "reg");
  EXPECT_NE(wi[1], "wire");
}

// Table 21-11: bit masquerades as reg, dumped with the total size of its packed
// dimension. This also covers the prose rule that a packed array is dumped as a
// single reg vector with its multiple packed dimensions collapsed into one: a
// bit [3:0][7:0] object presents as a single 32-bit reg vector, never as nested
// ranges. (logic maps to reg as well, but §21.7.2.1 fixes the pipeline
// registration of a 4-state logic variable to the net default; see
// LogicVariableMapsToRegAtWriterStage.)
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

  // The two packed dimensions collapse to one 32-bit reg vector.
  auto word = VarDecl(content, "word");
  ASSERT_EQ(word.size(), 6u) << content;
  EXPECT_EQ(word[1], "reg");
  EXPECT_EQ(word[2], "32");

  // Negative: a packed vector masquerades as reg, never the net keyword wire.
  EXPECT_NE(flags[1], "wire");
}

// Table 21-11: the default (untyped) enum maps to integer with size 32,
// independent of how few members it declares.
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

// §21.7.5: if an enum declaration specifies a type, it is dumped as that type
// rather than the default integer/32. An `enum bit [3:0]` is dumped as its base
// type -- reg with the base type's 4-bit width -- not integer/32.
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
  // Dumped as the specified base type bit[3:0] -> reg/4.
  EXPECT_EQ(e[1], "reg");
  EXPECT_EQ(e[2], "4");
  // Negative: the specified base type overrides the default enum mapping, so it
  // is not dumped as integer/32.
  EXPECT_NE(e[1], "integer");
  EXPECT_NE(e[2], "32");
}

// §21.7.5: the mapping follows the resolved type, so a type reached through a
// typedef is dumped as the type it names, not the net default a named type
// would otherwise fall to. A typedef of an untyped enum maps to integer/32
// (Table 21-11 default), and a typedef of an enum with a specified base type is
// dumped as that base type -- reg with the base width. Enums are most often
// declared this way, so the typedef path is exercised end-to-end.
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
  // Typedef of an untyped enum -> the default integer/32.
  auto c = VarDecl(content, "c");
  ASSERT_EQ(c.size(), 6u) << content;
  EXPECT_EQ(c[1], "integer");
  EXPECT_EQ(c[2], "32");

  // Typedef of an enum with a bit[3:0] base -> that base type, reg/4, not the
  // wire a named type would default to nor the integer/32 default enum mapping.
  auto n = VarDecl(content, "n");
  ASSERT_EQ(n.size(), 6u) << content;
  EXPECT_EQ(n[1], "reg");
  EXPECT_EQ(n[2], "4");
  EXPECT_NE(n[1], "wire");
  EXPECT_NE(n[1], "integer");
}

// §21.7.5: a packed structure is dumped as a single vector of reg (Table 21-11
// prose), like a packed array collapsed to one dimension. A packed struct of a
// byte and a 4-bit field presents as one 12-bit reg vector.
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
  // Negative: the whole packed struct is one vector, not the net default.
  EXPECT_NE(s[1], "wire");
}

// Table 21-11: shortreal masquerades as the real type, carrying its own 32-bit
// stored width in the size field. Driven end-to-end so the classification comes
// from the declared type rather than a hand-set tag. (Plain real is a 1364-2005
// type that needs no masquerade, so it is not a row of Table 21-11 and is not
// re-observed here.)
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

  // Negative: a shortreal is not dumped as an integral reg/integer, nor as the
  // wire an unmapped object would default to.
  EXPECT_NE(sr[1], "reg");
  EXPECT_NE(sr[1], "integer");
  EXPECT_NE(sr[1], "wire");
}

// §21.7.5: unpacked arrays and automatic variables are not dumped. An unpacked
// array declared beside a scalar contributes no $var declaration, and an
// automatic variable local to a function is likewise never surfaced to the
// dump, while the scalar is dumped normally. This confirms the object-selection
// stage never registers either kind.
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
  // The scalar is dumped as its mapped type.
  auto scalar_v = VarDecl(content, "scalar_v");
  ASSERT_EQ(scalar_v.size(), 6u) << content;
  EXPECT_EQ(scalar_v[1], "integer");

  // The unpacked array contributes no declaration, neither the whole array nor
  // any element shadow.
  EXPECT_FALSE(HasVar(content, "mem"));
  for (const auto& l : Lines(content)) {
    EXPECT_EQ(l.find(" mem"), std::string::npos) << "array reached dump: " << l;
  }
  // The function-local automatic variable is not dumped.
  EXPECT_FALSE(HasVar(content, "local_tmp"));
}

// Table 21-11 sizes bit by the total packed dimension, so a bit declared with
// no packed range is a one-bit reg. This is the scalar declaration form, which
// takes a different value-change path in the writer than the vector form, and
// it pins the size to the declared width rather than any fixed table size.
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

// §21.7.5: a typed enum takes its base type's mapping. The base type may be a
// fixed-width integer keyword rather than a packed vector, so a byte-based enum
// is dumped as that base -- reg/8 -- distinct from both the integer/32 default
// and the reg/4 a bit[3:0] base gives.
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
  // Negative: the specified base replaces the default enum mapping.
  EXPECT_NE(e[1], "integer");
  EXPECT_NE(e[2], "32");
}

// §21.7.5: a packed structure collapses to one reg vector whether it is written
// inline or reached through a typedef -- the mapping follows the resolved type,
// not the spelling of the declaration.
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

// §21.7.5: the mapping is fixed by the declared type, so it is unchanged by the
// syntactic position of the declaration. A declaration that carries an
// initializer takes a different lowering path than a bare one, yet the var_type
// and size written for it are the same.
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

// §21.7.5: the mapping follows the declared type in every syntactic position a
// dumped object can be declared in, including a module port header rather than
// a module-body declaration.
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

// Dependency end-to-end (§21.7.2.3): the node information a mapped $var carries
// sits inside the $scope/$upscope section that subclause defines, built here
// from a real module declaration rather than a hand-driven scope call. The
// mapped declarations must appear between the scope opener and its $upscope, so
// the Table 21-11 keyword and the enclosing section agree.
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

  // Both mapped declarations lie within the module's scope section.
  auto counter_pos = content.find(" counter $end");
  auto tag_pos = content.find(" tag $end");
  ASSERT_NE(counter_pos, std::string::npos) << content;
  ASSERT_NE(tag_pos, std::string::npos) << content;
  EXPECT_GT(counter_pos, scope_pos);
  EXPECT_LT(counter_pos, upscope_pos);
  EXPECT_GT(tag_pos, scope_pos);
  EXPECT_LT(tag_pos, upscope_pos);

  // And they carry the Table 21-11 mapping inside that section.
  auto counter_decl = VarDecl(content, "counter");
  ASSERT_EQ(counter_decl.size(), 6u) << content;
  EXPECT_EQ(counter_decl[1], "integer");
  auto tag_decl = VarDecl(content, "tag");
  ASSERT_EQ(tag_decl.size(), 6u) << content;
  EXPECT_EQ(tag_decl[1], "reg");
  EXPECT_EQ(tag_decl[2], "8");
}

// ---------------------------------------------------------------------------
// Writer-stage coverage for the two facets the model cannot supply from source.
// ---------------------------------------------------------------------------

Variable* MakeVar(Arena& arena, uint32_t width) {
  auto* v = arena.Create<Variable>();
  v->value = MakeLogic4VecVal(arena, width, 0);
  return v;
}

// Table 21-11: logic masquerades as reg. §21.7.2.1 fixes the pipeline
// registration of a 4-state logic variable to the net var_type default (its
// end-to-end tests pin `logic` -> wire), so the mapping of a logic-typed object
// to reg is observed here at the writer stage, where the data type is supplied
// directly. This is the writer half of the same rule the integral e2e tests
// above drive from source for bit.
TEST_F(VcdTypeMappingSim, LogicVariableMapsToRegAtWriterStage) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal(VcdSignalSpec{"lv", 8, MakeVar(arena_, 8),
                                     NetType::kWire, -1, -1,
                                     VcdDataType::kLogic});
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  auto lv = VarDecl(content, "lv");
  ASSERT_EQ(lv.size(), 6u) << content;
  EXPECT_EQ(lv[1], "reg");
  EXPECT_EQ(lv[2], "8");
}

// §21.7.5: an unpacked structure appears as a named fork-join block, so it is
// easy to distinguish from a begin-end block, and its member elements appear as
// their mapped types. Driven from a real unpacked struct declaration: the
// structure contributes no object of its own, its scope carries the fork
// keyword rather than module, and each member is declared inside that scope
// under the Table 21-11 mapping for its own type.
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
  // The structure opens a fork-join scope, not a module scope, and is not
  // itself dumped as one flat object.
  EXPECT_NE(content.find("$scope fork pkt $end"), std::string::npos) << content;
  EXPECT_EQ(content.find("$scope module pkt $end"), std::string::npos);
  EXPECT_FALSE(HasVar(content, "pkt"));

  // Each member is declared under its own type's mapping.
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

  // The members are declared between the fork scope and its $upscope.
  auto fork_pos = content.find("$scope fork pkt $end");
  auto up_pos = content.find("$upscope $end", fork_pos);
  ASSERT_NE(up_pos, std::string::npos) << content;
  auto header_pos = content.find(" header $end");
  ASSERT_NE(header_pos, std::string::npos) << content;
  EXPECT_GT(header_pos, fork_pos);
  EXPECT_LT(header_pos, up_pos);
}

// §21.7.5: a member of an unpacked structure is a dumped object in its own
// right, so each member carries its own identifier code and reports its own
// value. The members share one backing value in the model, so this pins that a
// member's value is sliced out of that shared value rather than the whole
// structure being reported under each member's code.
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
  // Distinct identifier codes: each member is its own dumped object.
  EXPECT_NE(header[3], valid[3]);

  // The byte member's own new value (8'h5A) is recorded against the member's
  // identifier, sliced out of the structure's shared value.
  auto lines = Lines(content);
  bool saw_header_change = false;
  for (const auto& l : lines) {
    if (l == "b1011010 " + header[3]) saw_header_change = true;
  }
  EXPECT_TRUE(saw_header_change) << content;
}

}  // namespace
}  // namespace delta
