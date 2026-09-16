#pragma once

namespace delta {

class Arena;
class DiagEngine;
struct ModuleItem;
class PropertyRegistry;
struct RtlirModule;

// §16.14.6: the concurrent assertion statements embedded in the procedure
// `procedure`, an initial or an always of `mod`, made ready for the run:
// one whose property_spec instantiates a named property or sequence takes
// its body as a static statement's does (§16.12.1), and one whose spec
// opens with no clocking event takes the leading clocking event of its
// evaluation from the procedure, where the procedure holds no blocking
// timing control, exactly one event control and, among that control's
// event expressions, exactly one that is solely an event variable or a
// clocking block identifier, or an edge over an expression with an
// optional iff, whose terms the procedure references nowhere else but as a
// clocking event or within an assertion statement; and, where the
// procedure gives none, from the default clocking of `mod` as if the
// assertion stood before the procedure. A statement left with no clock is
// reported, the clause making that an error.
void ElaborateProceduralConcurrentAssertions(ModuleItem* procedure,
                                             const RtlirModule* mod,
                                             const PropertyRegistry& registry,
                                             Arena& arena, DiagEngine& diag);

// §16.17: the same for the expect statements of the task or function
// `subroutine`, which §16.17 has appear wherever a wait statement can; a
// subroutine gives no contextually inferred clock, so a spec that opens
// with none takes the default clocking of `mod`.
void ElaborateSubroutineConcurrentAssertions(ModuleItem* subroutine,
                                             const RtlirModule* mod,
                                             const PropertyRegistry& registry,
                                             Arena& arena, DiagEngine& diag);

}  // namespace delta
