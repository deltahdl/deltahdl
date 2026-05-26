#pragma once

#include <cstddef>
#include <string_view>
#include <unordered_map>

#include "parser/ast.h"

namespace delta {

// §F.4.2 describes flattening a checker that contains instances of other
// checkers into a single checker without instances. The substitution of
// actual arguments targets the formal *input* arguments only: formal
// arguments with output direction are treated differently (see §17.2) and the
// rewriting algorithm does not apply to them. As with §F.4.1, a flattened
// checker that is not legal makes its source not legal.

struct FlattenedChecker {
  std::string_view name;
  // Formals the algorithm rewrites by substituting actual arguments.
  std::size_t input_formal_count = 0;
  // Output-direction formals the algorithm does not apply to (see §17.2).
  std::size_t output_formal_count = 0;
  // Checker instances still present in the body; the flattened result is a
  // checker without instances, so a fully flattened checker reports zero.
  int remaining_instances = 0;
  bool legal = false;
};

class CheckerRegistry {
 public:
  void Register(const ModuleDecl* decl);

  const ModuleDecl* Find(std::string_view name) const;

  // §F.4.2: a formal argument with output direction is treated differently
  // (see §17.2) and the rewriting algorithm does not apply to it. Every other
  // formal is an input formal that the algorithm rewrites.
  static bool AlgorithmAppliesToFormal(const PortDecl& formal);

  // Number of formals the algorithm substitutes (the input formals).
  std::size_t InputFormalCount(const ModuleDecl* decl) const;

  // Number of output-direction formals the algorithm leaves untouched.
  std::size_t OutputFormalCount(const ModuleDecl* decl) const;

  // §F.4.2: the algorithm targets checkers that contain instances of other
  // checkers. Returns how many such checker instances appear in the body.
  int CheckerInstanceCount(const ModuleDecl* decl) const;

  // Models the flattened result for `actual_input_arg_count` actual arguments
  // bound to the checker's input formals. Output formals are never bound here.
  FlattenedChecker Flatten(std::string_view name,
                           std::size_t actual_input_arg_count) const;

  // §F.4.2: a checker rewritten by the algorithm may be a nested checker
  // instance or a top-level checker instance; either placement is acceptable
  // once the flattened checker is legal.
  static bool IsAcceptableAsCheckerInstance(const FlattenedChecker& fc);

 private:
  std::unordered_map<std::string_view, const ModuleDecl*> by_name_;
};

}  // namespace delta
