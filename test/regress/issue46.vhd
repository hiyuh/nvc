entity issue46 is
begin
	assert (1.0 * 1 = 1.0);
	assert (1 * 1.0 = 1.0);
	assert (1.0 / 1 = 1.0);
	assert (2.0 * 1 = 2.0);
	assert (1 * 2.0 = 2.0);
	assert (2.0 / 1 = 2.0);
end entity issue46;

architecture a of issue46 is
begin
end architecture a;
