entity reduced_image is
end entity;

architecture test of reduced_image is
begin

    process is
    begin
        report integer'image(4);
        wait;
    end process;
    
end architecture;
