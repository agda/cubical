check: $(wildcard **/*.agda)
	agda Cubical/Core/Everything.agda

clean:; rm -f */*agdai */*/*agdai
