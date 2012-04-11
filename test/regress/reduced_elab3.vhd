entity reduced_elab3 is
end entity;

architecture test of reduced_elab3 is
    signal x : integer;
begin

    process is
    begin
        report x'instance_name;
        wait;
    end process;

end architecture;

