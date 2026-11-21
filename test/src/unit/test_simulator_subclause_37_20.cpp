#include <gtest/gtest.h>

#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::vector<VpiHandle> Collect(VpiContext& ctx, VpiHandle iterator) {
  std::vector<VpiHandle> objects;
  if (!iterator) return objects;
  while (VpiHandle next = ctx.Scan(iterator)) objects.push_back(next);
  return objects;
}

TEST(MemoryModel, MemoryWordIterationReachesRegWords) {
  VpiContext ctx;

  VpiObject word0;
  word0.type = vpiReg;
  VpiObject left_range;
  left_range.type = vpiConstant;
  VpiObject word1;
  word1.type = vpiReg;

  VpiObject reg_array;
  reg_array.type = vpiRegArray;
  reg_array.children = {&word0, &left_range, &word1};

  std::vector<VpiHandle> words =
      Collect(ctx, ctx.Iterate(vpiMemoryWord, &reg_array));
  ASSERT_EQ(words.size(), 2u);
  EXPECT_EQ(words[0], &word0);
  EXPECT_EQ(words[1], &word1);
  EXPECT_EQ(words[0]->type, vpiReg);
  EXPECT_EQ(words[1]->type, vpiReg);
}

TEST(MemoryModel, MemoryWordIterationNullWhenNoWords) {
  VpiContext ctx;

  VpiObject reg_array;
  reg_array.type = vpiRegArray;
  EXPECT_EQ(ctx.Iterate(vpiMemoryWord, &reg_array), nullptr);
}

TEST(MemoryModel, MemoryWordIterationGatedToRegArray) {
  VpiContext ctx;

  VpiObject word;
  word.type = vpiReg;
  VpiObject not_an_array;
  not_an_array.type = vpiModule;
  not_an_array.children = {&word};

  EXPECT_EQ(ctx.Iterate(vpiMemoryWord, &not_an_array), nullptr);
}

TEST(MemoryPublic, MemoryIterationReturnsRegArrayObjects) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject word;
  word.type = vpiReg;
  VpiObject memory;
  memory.type = vpiRegArray;
  memory.children = {&word};
  VpiObject plain;
  plain.type = vpiReg;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&plain, &memory};

  vpiHandle it = vpi_iterate(vpiMemory, VpiHandleOf(&scope));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &memory);
  EXPECT_EQ(vpi_scan(it), nullptr);

  SetGlobalVpiContext(nullptr);
}

TEST(MemoryPublic, MemoryIterationIsNullWhenTheScopeHasNoArray) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject plain;
  plain.type = vpiReg;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&plain};

  EXPECT_EQ(vpi_iterate(vpiMemory, VpiHandleOf(&scope)), nullptr);

  SetGlobalVpiContext(nullptr);
}

TEST(MemoryPublic, IsMemoryDistinguishesARegArrayFromAnyOtherArray) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject reg_word;
  reg_word.type = vpiReg;
  VpiObject memory;
  memory.type = vpiRegArray;
  memory.children = {&reg_word};
  EXPECT_EQ(vpi_get(vpiIsMemory, VpiHandleOf(&memory)), 1);

  VpiObject int_word;
  int_word.type = vpiIntVar;
  VpiObject int_array;
  int_array.type = vpiArrayVar;
  int_array.children = {&int_word};
  EXPECT_EQ(vpi_get(vpiIsMemory, VpiHandleOf(&int_array)), 0);

  VpiObject not_an_array;
  not_an_array.type = vpiReg;
  EXPECT_EQ(vpi_get(vpiIsMemory, VpiHandleOf(&not_an_array)), 0);

  SetGlobalVpiContext(nullptr);
}

class MemoriesOfARun : public VpiDesignRun {
 protected:
  static void ExpectOnlyArr(vpiHandle scope, const char* label) {
    ASSERT_NE(scope, nullptr) << label;
    EXPECT_EQ(NamesOf(vpiMemory, scope), std::vector<std::string>{"arr"})
        << label;
    EXPECT_EQ(KindsOf(vpiMemory, scope), std::vector<int>{vpiRegArray})
        << label;
  }

  static std::vector<int> WordIndices(vpiHandle memory) {
    std::vector<int> indices;
    for (vpiHandle word : ObjectsOf(vpiMemoryWord, memory)) {
      indices.push_back(IntegerOf(vpi_handle(vpiIndex, word)));
    }
    return indices;
  }

  static std::vector<int> LeftAndRight(vpiHandle obj) {
    vpiHandle left = vpi_handle(vpiLeftRange, obj);
    vpiHandle right = vpi_handle(vpiRightRange, obj);
    if (left == nullptr || right == nullptr) return {};
    return {IntegerOf(left), IntegerOf(right)};
  }

  static vpiHandle UnnamedBlockOf(vpiHandle scope) {
    for (vpiHandle process : ObjectsOf(vpiProcess, scope)) {
      vpiHandle stmt = vpi_handle(vpiStmt, process);
      if (stmt != nullptr && vpi_get(vpiType, stmt) == vpiBegin) return stmt;
    }
    return nullptr;
  }
};

constexpr const char* kArraysOfEveryScope =
    "logic arr [2]; int i;\n"
    "package pk; logic arr [2]; int i; endpackage\n"
    "interface intf; logic arr [2]; int i; endinterface\n"
    "program prog; logic arr [2]; int i; endprogram\n"
    "module top; intf i0(); prog p0();\n"
    "  class C; logic arr [2]; int i; endclass\n"
    "  C c = new;\n"
    "  task t; logic arr [2]; int i; endtask\n"
    "  function void f; logic arr [2]; int i; endfunction\n"
    "  if (1) begin : g logic arr [2]; int i; end\n"
    "  initial begin : nb logic arr [2]; int i; end\n"
    "  initial fork : nf logic arr [2]; int i; join\n"
    "  initial begin logic arr [2]; int i; end\n"
    "endmodule\n";

TEST_F(MemoriesOfARun, AMemoryWordReachesItsIndex) {
  Run("module top;\n"
      "  reg [7:0] mem [4:7];\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiMemoryWord, By("top.mem"));
  ASSERT_NE(it, nullptr);
  vpi_scan(it);
  vpi_scan(it);
  vpiHandle word = vpi_scan(it);
  ASSERT_NE(word, nullptr);
  vpi_free_object(it);
  vpiHandle index = vpi_handle(vpiIndex, word);
  ASSERT_NE(index, nullptr);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(index, &value);
  EXPECT_EQ(value.value.integer, 6);
}

TEST_F(MemoriesOfARun, AModuleIteratesEachOfItsArraysAsARegArray) {
  Run("module top; reg [7:0] mem [0:3]; reg [7:0] v; int a [4];\n"
      "  reg [7:0] m [2][3]; bit [3:0] b [2]; int i;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  EXPECT_EQ(NamesOf(vpiMemory, top),
            (std::vector<std::string>{"a", "b", "m", "mem"}));
  EXPECT_EQ(KindsOf(vpiMemory, top), std::vector<int>(4, vpiRegArray));
}

TEST_F(MemoriesOfARun, ASubroutineBlockGenerateOrPackageIteratesItsArrays) {
  Run(kArraysOfEveryScope);
  vpiHandle top = By("top");
  ExpectOnlyArr(Named(vpiTaskFunc, top, "t"), "t");
  ExpectOnlyArr(Named(vpiTaskFunc, top, "f"), "f");
  ExpectOnlyArr(By("top.g"), "g");
  ExpectOnlyArr(By("top.nb"), "nb");
  ExpectOnlyArr(By("pk"), "pk");
}

TEST_F(MemoriesOfARun, AnInterfaceOrProgramIteratesItsArrays) {
  Run(kArraysOfEveryScope);
  ExpectOnlyArr(By("top.i0"), "i0");
  ExpectOnlyArr(By("top.p0"), "p0");
}

TEST_F(MemoriesOfARun, AForkOrADeclaringUnnamedBlockIteratesItsArrays) {
  Run(kArraysOfEveryScope);
  ExpectOnlyArr(By("top.nf"), "nf");
  vpiHandle unnamed = UnnamedBlockOf(By("top"));
  ASSERT_NE(unnamed, nullptr);
  EXPECT_EQ(vpi_get_str(vpiName, unnamed), nullptr);
  ExpectOnlyArr(unnamed, "unnamed begin");
}

TEST_F(MemoriesOfARun, AClassIteratesItsArrayProperties) {
  Run(kArraysOfEveryScope);
  ExpectOnlyArr(Named(vpiClassDefn, By("top"), "C"), "defn");
  ExpectOnlyArr(vpi_handle(vpiClassObj, By("top.c")), "obj");
  vpiHandle typespec = vpi_handle(vpiTypespec, By("top.c"));
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiClassTypespec);
  ExpectOnlyArr(typespec, "typespec");
}

TEST_F(MemoriesOfARun, TheCompilationUnitIteratesItsArrays) {
  Run(kArraysOfEveryScope);
  ExpectOnlyArr(Named(vpiPackage, nullptr, "$unit"), "$unit");
}

TEST_F(MemoriesOfARun, AScopeWithNoArrayIteratesNoMemory) {
  Run("module top; reg [7:0] v; int i;\n"
      "  task t; int j; endtask\n"
      "  initial begin : nb int k; end\n"
      "  if (1) begin : g reg [3:0] w [2]; end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(Named(vpiTaskFunc, top, "t"), nullptr);
  ASSERT_NE(By("top.nb"), nullptr);
  EXPECT_EQ(vpi_iterate(vpiMemory, top), nullptr);
  EXPECT_EQ(vpi_iterate(vpiMemory, Named(vpiTaskFunc, top, "t")), nullptr);
  EXPECT_EQ(vpi_iterate(vpiMemory, By("top.nb")), nullptr);
}

TEST_F(MemoriesOfARun, AMemoryIteratesItsWordsAsRegsInDeclaredOrder) {
  Run("module top; reg [7:0] up [4:7]; reg [7:0] down [7:4];\n"
      "  logic [3:0] lm [1:2]; reg bits [0:1];\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiMemoryWord, By("top.up")), std::vector<int>(4, vpiReg));
  EXPECT_EQ(WordIndices(By("top.up")), (std::vector<int>{4, 5, 6, 7}));
  EXPECT_EQ(KindsOf(vpiMemoryWord, By("top.down")),
            std::vector<int>(4, vpiReg));
  EXPECT_EQ(WordIndices(By("top.down")), (std::vector<int>{7, 6, 5, 4}));
  EXPECT_EQ(KindsOf(vpiMemoryWord, By("top.lm")), std::vector<int>(2, vpiReg));
  EXPECT_EQ(WordIndices(By("top.lm")), (std::vector<int>{1, 2}));
  EXPECT_EQ(KindsOf(vpiMemoryWord, By("top.bits")),
            std::vector<int>(2, vpiReg));
  EXPECT_EQ(WordIndices(By("top.bits")), (std::vector<int>{0, 1}));
}

TEST_F(MemoriesOfARun, AOneDimensionalRegArrayIsAMemory) {
  Run("module top; reg [7:0] mem [0:3]; reg bits [0:3]; logic [3:0] lm [2];\n"
      "endmodule\n");
  for (const char* name : {"top.mem", "top.bits", "top.lm"}) {
    EXPECT_EQ(vpi_get(vpiIsMemory, By(name)), 1) << name;
  }
}

TEST_F(MemoriesOfARun, NoOtherVariableIsAMemory) {
  Run("module top; reg [7:0] m [2][3]; bit [7:0] b [4]; int a [4];\n"
      "  reg [7:0] v;\n"
      "endmodule\n");
  for (const char* name : {"top.m", "top.b", "top.a", "top.v"}) {
    EXPECT_EQ(vpi_get(vpiIsMemory, By(name)), 0) << name;
  }
}

TEST_F(MemoriesOfARun, AMemorysRangeIsItsLeftmostUnpackedDimension) {
  Run("module top; reg [7:0] up [4:7]; reg [7:0] down [7:4];\n"
      "  reg [7:0] m [1:2][5:3];\n"
      "endmodule\n");
  EXPECT_EQ(LeftAndRight(By("top.up")), (std::vector<int>{4, 7}));
  EXPECT_EQ(LeftAndRight(By("top.down")), (std::vector<int>{7, 4}));
  EXPECT_EQ(LeftAndRight(By("top.m")), (std::vector<int>{1, 2}));
}

TEST_F(MemoriesOfARun, DISABLED_AMemoryWordsRangeIsItsPackedRange) {
  Run("module top; reg [7:0] mem [4:7]; reg [1:4] asc [0:1];\n"
      "endmodule\n");
  const std::vector<vpiHandle> kMem = ObjectsOf(vpiMemoryWord, By("top.mem"));
  const std::vector<vpiHandle> kAsc = ObjectsOf(vpiMemoryWord, By("top.asc"));
  ASSERT_EQ(kMem.size(), 4U);
  ASSERT_EQ(kAsc.size(), 2U);
  EXPECT_EQ(LeftAndRight(kMem[2]), (std::vector<int>{7, 0}));
  EXPECT_EQ(LeftAndRight(kAsc[1]), (std::vector<int>{1, 4}));
}

TEST_F(MemoriesOfARun, AnUnrangedMemoryWordHasNoRange) {
  Run("module top; reg bits [0:3]; endmodule\n");
  const std::vector<vpiHandle> kWords =
      ObjectsOf(vpiMemoryWord, By("top.bits"));
  ASSERT_EQ(kWords.size(), 4U);
  EXPECT_EQ(vpi_handle(vpiLeftRange, kWords[1]), nullptr);
  EXPECT_EQ(vpi_handle(vpiRightRange, kWords[1]), nullptr);
}

TEST_F(MemoriesOfARun, AnIteratedWordsParentIsItsMemory) {
  Run("module top; reg [7:0] mem [4:7]; endmodule\n");
  vpiHandle mem = By("top.mem");
  const std::vector<vpiHandle> kWords = ObjectsOf(vpiMemoryWord, mem);
  ASSERT_EQ(kWords.size(), 4U);
  for (vpiHandle word : kWords) {
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, word)), VpiObjectOf(mem));
  }
}

TEST_F(MemoriesOfARun, AWordReachedByIndexHasItsMemoryAsParent) {
  Run("module top; reg [7:0] mem [4:7]; endmodule\n");
  vpiHandle mem = By("top.mem");
  vpiHandle word = vpi_handle_by_index(mem, 6);
  ASSERT_NE(word, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, word)), VpiObjectOf(mem));
}

TEST_F(MemoriesOfARun, AnIndexSelectsTheWordDeclaredAtIt) {
  Run("module top; reg [7:0] mem [4:7]; reg [7:0] down [7:4];\n"
      "  initial begin mem[4] = 10; mem[5] = 11; mem[6] = 12; mem[7] = 13;\n"
      "    down[7] = 20; down[6] = 21; down[5] = 22; down[4] = 23; end\n"
      "endmodule\n");
  vpiHandle mem_5 = vpi_handle_by_index(By("top.mem"), 5);
  vpiHandle down_5 = vpi_handle_by_index(By("top.down"), 5);
  ASSERT_NE(mem_5, nullptr);
  ASSERT_NE(down_5, nullptr);
  EXPECT_EQ(vpi_get(vpiType, mem_5), vpiReg);
  EXPECT_EQ(IntegerOf(mem_5), 11);
  EXPECT_EQ(IntegerOf(down_5), 22);
  EXPECT_EQ(vpi_handle_by_index(By("top.mem"), 0), nullptr);
  EXPECT_EQ(vpi_handle_by_index(By("top.mem"), 3), nullptr);
}

TEST_F(MemoriesOfARun, IndicesSelectTheWordOfAMultidimensionalArray) {
  Run("module top; reg [7:0] m [2][3];\n"
      "  initial for (int i = 0; i < 2; i++)\n"
      "    for (int j = 0; j < 3; j++) m[i][j] = 10 * i + j;\n"
      "endmodule\n");
  PLI_INT32 one_two[] = {1, 2};
  PLI_INT32 two_one[] = {2, 1};
  vpiHandle word = vpi_handle_by_multi_index(By("top.m"), 2, one_two);
  ASSERT_NE(word, nullptr);
  EXPECT_EQ(vpi_get(vpiType, word), vpiReg);
  EXPECT_EQ(IntegerOf(word), 12);
  EXPECT_EQ(vpi_handle_by_multi_index(By("top.m"), 2, two_one), nullptr);
}

TEST_F(MemoriesOfARun, AModulesMemoryReachesTheModuleAsBoth) {
  Run("module top; reg [7:0] mem [0:3]; endmodule\n");
  vpiHandle mem = By("top.mem");
  ASSERT_NE(mem, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, mem)), VpiObjectOf(By("top")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, mem)), VpiObjectOf(By("top")));
}

TEST_F(MemoriesOfARun, ANestedMemoryReachesItsScopeAndItsModule) {
  Run("module top;\n"
      "  initial begin : blk reg [7:0] bm [0:3]; end\n"
      "  task t; reg [7:0] tm [0:1]; endtask\n"
      "  function void f; reg [7:0] fm [0:1]; endfunction\n"
      "  if (1) begin : g reg [7:0] gm [0:1]; end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const std::vector<std::pair<vpiHandle, const char*>> kScopes = {
      {By("top.blk"), "bm"},
      {Named(vpiTaskFunc, top, "t"), "tm"},
      {Named(vpiTaskFunc, top, "f"), "fm"},
      {By("top.g"), "gm"}};
  for (const auto& [scope, name] : kScopes) {
    ASSERT_NE(scope, nullptr) << name;
    vpiHandle memory = Named(vpiMemory, scope, name);
    ASSERT_NE(memory, nullptr) << name;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, memory)), VpiObjectOf(scope))
        << name;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, memory)), VpiObjectOf(top))
        << name;
  }
}

}  // namespace
}  // namespace delta
