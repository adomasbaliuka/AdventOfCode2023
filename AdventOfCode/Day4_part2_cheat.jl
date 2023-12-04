import DelimitedFiles

struct EvalCard
    idx::Int
    matches::Int
end

function parseCard(line)
    parts = split(strip(line), ":")
    idx = match(r".*\s+([0-9]+)", parts[1]).captures[1] |> s -> parse(Int, s)
    winHave = split(parts[2], "|")
    win = winHave[1]
    have = winHave[2]
    
    win = replace(win, r"\s+" => " ") |> strip
    have = replace(have, r"\s+" => " ") |> strip

    win = DelimitedFiles.readdlm(IOBuffer(win), Int)
    have = DelimitedFiles.readdlm(IOBuffer(have), Int)
    
    matches = length(win ∩ have)
    EvalCard(idx, matches)
end

function result_part_2(intput::String)
    lines = split(strip(intput), "\n")
    cards::Vector{EvalCard} = map(lines) do l
        parseCard(l)
    end

    i = 1
    while i < length(cards)
        currIdx = cards[i].idx
        nmatches = cards[i].matches
        toappend = map(1:nmatches) do m
            ii = findfirst(cards) do c
                c.idx == currIdx + m
            end
            cards[ii]
        end
        
        append!(cards, toappend)
        i += 1
    end
    return i
end
