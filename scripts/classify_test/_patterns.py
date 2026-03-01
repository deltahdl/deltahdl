"""Pattern table mapping test-body substrings to file-name prefixes.

Each entry is ``(substring, prefix)``.  The first matching substring
determines the pipeline-stage prefix used by ``_detect_prefix``.
"""

PREFIX_PATTERNS: list[tuple[str, str]] = [
    # Preprocessor
    ("Preprocess", "test_preprocessor_"),
    # Synthesizer
    ("SynthLower", "test_synthesizer_"),
    ("Aig", "test_synthesizer_"),
    # Elaborator
    ("Elaborate", "test_elaborator_"),
    ("ElabOk", "test_elaborator_"),
    ("ValidateNet", "test_elaborator_"),
    ("ValidateGate", "test_elaborator_"),
    ("ValidateRef", "test_elaborator_"),
    ("InferExprWidth", "test_elaborator_"),
    ("SensId", "test_elaborator_"),
    ("LongestStaticPrefix", "test_elaborator_"),
    ("ComputeArray", "test_elaborator_"),
    ("CollectExpr", "test_elaborator_"),
    ("MakeSelectExpr", "test_elaborator_"),
    ("HasErrors", "test_elaborator_"),
    ("ImplicitlySigned", "test_elaborator_"),
    # Parser
    ("Parse", "test_parser_"),
    ("CanHaveStrengthSpec", "test_parser_"),
    # Lexer
    ("Lex", "test_lexer_"),
    # Simulator: evaluation / runtime
    ("Eval", "test_simulator_"),
    ("CreateVariable", "test_simulator_"),
    ("RunAndGet", "test_simulator_"),
    ("RunStmt", "test_simulator_"),
    ("Execute", "test_simulator_"),
    ("ToUint64", "test_simulator_"),
    ("MakeInt", "test_simulator_"),
    ("MakeId", "test_simulator_"),
    ("MkInt", "test_simulator_"),
    ("MakeVar", "test_simulator_"),
    ("MakeBinary", "test_simulator_"),
    ("MakeClassType", "test_simulator_"),
    # Simulator: 4-state values / logic
    ("Logic4", "test_simulator_"),
    ("Val4", "test_simulator_"),
    # Simulator: variables / types
    ("AddVariable", "test_simulator_"),
    ("GetValue", "test_simulator_"),
    ("SysCall", "test_simulator_"),
    ("AddPlusArg", "test_simulator_"),
    ("RegisterEnum", "test_simulator_"),
    ("SvString", "test_simulator_"),
    ("DynArray", "test_simulator_"),
    ("AssocArray", "test_simulator_"),
    # Simulator: VPI / DPI
    ("Vpi", "test_simulator_"),
    ("Dpi", "test_simulator_"),
    # Simulator: scheduling / processes
    ("Scheduler", "test_simulator_"),
    ("SimContext", "test_simulator_"),
    ("CurrentTime", "test_simulator_"),
    ("SimTime", "test_simulator_"),
    ("Process", "test_simulator_"),
    ("Coroutine", "test_simulator_"),
    ("EventCoalescer", "test_simulator_"),
    ("Partitioner", "test_simulator_"),
    # Simulator: clocking / sensitivity
    ("Clocking", "test_simulator_"),
    ("Sensitivity", "test_simulator_"),
    ("EdgeKind", "test_simulator_"),
    # Simulator: gates / switches / primitives
    ("GateKind", "test_simulator_"),
    ("SwitchType", "test_simulator_"),
    ("Udp", "test_simulator_"),
    ("MakeNetPair", "test_simulator_"),
    ("Pullup", "test_simulator_"),
    ("Pulldown", "test_simulator_"),
    ("Strength", "test_simulator_"),
    # Simulator: delays / timing
    ("DelaySpec", "test_simulator_"),
    ("MinTypMax", "test_simulator_"),
    ("ComputeGateDelay", "test_simulator_"),
    ("TimingControl", "test_simulator_"),
    ("TimingCheck", "test_simulator_"),
    ("RepeatCount", "test_simulator_"),
    ("PathDelay", "test_simulator_"),
    ("SpecifyPath", "test_simulator_"),
    ("SdfAnnotate", "test_simulator_"),
    # Simulator: coverage
    ("Coverage", "test_simulator_"),
    ("CreateGroup", "test_simulator_"),
    ("Sample", "test_simulator_"),
    # Simulator: assertions
    ("Assertion", "test_simulator_"),
    ("SvaEngine", "test_simulator_"),
    # Simulator: VCD output
    ("VcdClause", "test_simulator_"),
    ("FormatModule", "test_simulator_"),
    # Simulator: nets / resolution
    ("ForceRelease", "test_simulator_"),
    ("Supply", "test_simulator_"),
    ("Trireg", "test_simulator_"),
    # Simulator: suite-name / fixture patterns
    ("SimCh", "test_simulator_"),
    ("SimFixture", "test_simulator_"),
    ("RealFixture", "test_simulator_"),
    ("ClassSim", "test_simulator_"),
    ("IpcSync", "test_simulator_"),
    ("DriverUpdate", "test_simulator_"),
    ("DataReadApi", "test_simulator_"),
    # Simulator: misc
    ("CompiledProcess", "test_simulator_"),
    ("Arena", "test_simulator_"),
    ("Callable", "test_simulator_"),
]
