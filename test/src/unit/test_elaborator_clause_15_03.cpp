#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.3: semaphore declaration elaborates with class_type_name set.
TEST(SemaphoreElaborator, DeclarationSetsClassTypeName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore smTx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "semaphore");
}

// §15.3: multiple semaphore declarations each get correct class_type_name.
TEST(SemaphoreElaborator, MultipleSemaphoreDeclarations) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore s1;\n"
      "  semaphore s2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[0].class_type_name, "semaphore");
  EXPECT_EQ(mod->variables[1].class_type_name, "semaphore");
}

// §15.3: semaphore with initializer elaborates without error.
TEST(SemaphoreElaborator, DeclarationWithInitializer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem = new(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "semaphore");
  EXPECT_NE(mod->variables[0].init_expr, nullptr);
}

// §15.3: semaphore used in initial block with method calls elaborates.
TEST(SemaphoreElaborator, MethodCallsInInitialBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem;\n"
      "  initial begin\n"
      "    sem.put(1);\n"
      "    sem.get();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.3: semaphore does not require an explicit class declaration.
TEST(SemaphoreElaborator, BuiltInTypeWithoutClassDecl) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  semaphore s;\n"
      "endmodule\n"));
}

}  // namespace
