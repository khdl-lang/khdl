import khdl


def test_imported_interface_field_indexed_assignment():
    # regression test:
    #   indexing into an interface field whose type is declared
    #   in another file used to panic while joining spans across files
    types_src = """
    pub interface Data {
        values: [2]uint(8),
        view Source { values: out }
    }
    """
    top_src = """
    import types.[Data];
    pub module top ports(clk: in clock, output: interface sync(clk) Data.Source) {
        clocked(clk) {
            reg wire output.values = undef;
            output.values[0] = 0;
            output.values[1] = 1;
        }
    }
    """

    source = khdl.Source()
    source.add_source_content(["types"], "types.kh", types_src)
    source.add_source_content(["top"], "top.kh", top_src)
    top: khdl.Module = source.compile().resolve("top.top")
    assert top is not None
