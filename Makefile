check: $(wildcard **/*.agda)
	runghc GenerateEverything.hs
	agda Cubical/Core/Everything.agda
	agda Cubical/Basics/Everything.agda
	agda Cubical/HITs/Everything.agda

clean:; rm -f */*agdai */*/*agdai
