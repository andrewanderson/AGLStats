package main

import (
	"bufio"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io/ioutil"
	"math"
	"net/http"
	"net/url"
	"os"
	"sort"
	"strconv"
	"strings"
	"time"

	"golang.org/x/oauth2/google"
	"google.golang.org/api/sheets/v4"

	"github.com/dgraph-io/badger"
)

type DeckSlot struct {
	amount   int
	cardName string
	card     *ScryfallCard
}

type PlayerPool struct {
	player  string
	record  string
	uri     string
	isAlive bool
	team    string
	cards   []DeckSlot
	facts   map[string]int
}

type CardStrength struct {
	cardName string
	strength float64
}

// Constants that shouldn't change
const googleApiSecretFile = "D:\\Code\\PoolParser\\asl-pools-859d88f87aef.json"
const sealedDeckApiUriTemplate string = "https://sealeddeck.tech/api/pools/%s"
const sealedDeckPauseMs = 100                                                       // be a good citizen
const scryfallCardTemplate string = "https://api.scryfall.com/cards/named?exact=%s" // lookup for an exact card = sub in +'s for spaces
const scryfallSetClauseTemplate string = "&set=%s"                                  // append on to scryfallCardTemplate when needed
const scryfallPauseMs = 75                                                          // be a good citizen
const seventeenLandsTemplate string = "https://www.17lands.com/card_ratings/data?expansion=%s&format=%s&start_date=2019-01-01&end_date=%s&colors=%s"
const seventeenLandsPauseMs = 1000
const seventeenLandsDrawnThreshold = 100 // 1000 is a typical base.  Will be modified for rarity
const webRetires int = 3
const webRetryMs = 500

const dbPath = "D:\\Code\\PoolParser\\db"
const outputPath = "D:\\Code\\PoolParser\\out"
const perfOutputPath = "D:\\Code\\PoolParser\\out-perf"
const debugging17Lands = false

// League-specific constants
const leagueSheetID string = "1cNoZe15TjOgmtTsbH1R3nX_YU9Q9E224bjVUEV0haDk"
const poolLinkRange string = "Pools!A7:H67"
const sheetPlayerColumnIndex = 0
const sheetWinColumnIndex = 2
const sheetLossColumnIndex = 3
const sheetLinkColumnIndex = 4
const leagueEliminationLosses = 11
const deckStrengthCardsToConsider = 60

// We want to track a stat for fun.  Here are some lists that we're using
var bombList map[string]DeckSlot
var bombSealedDeckId = fmt.Sprintf(sealedDeckApiUriTemplate, "PSYLhA4Tit") //Hdw62MnDDd
var dudList map[string]DeckSlot
var dudSealedDeckId = fmt.Sprintf(sealedDeckApiUriTemplate, "Ga4qDQMx6I")
var topCommonList map[string]DeckSlot
var topCommonDeckId = fmt.Sprintf(sealedDeckApiUriTemplate, "fKAvpTdSeX")

// Perf data variables for deck strength calculations
var mtg2CDecks = []string{"WU", "WB", "WR", "WG", "UB", "UR", "UG", "BR", "BG", "RG"}
var mtg3CDecks = []string{"WUB", "WUR", "WUG", "BRW", "GWB", "WRG", "UBR", "UBG", "RGU", "BRG"}
var allSeventeenLandsSets = []string{"DOM", "M19", "RNA", "GRN", "WAR", "M20", "ELD", "THB", "IKO", "M21", "AKR", "ZNR", "KLR", "KHM", "STX", "AFR", "MID", "VOW", "NEO", "SNC", "HBG"} // keep ordered by release
var seventeenLands3CSets = map[string]struct{}{"SNC": {}}
var currentSet = "HBG"
var setPerformanceFormat = "PremierDraft"
var leagueIsMonoSet = false // Should we bother looking up other sets?
var setsInPools map[string]int = make(map[string]int)

func main() {
	// Open the local badger database
	db, err := badger.Open(badger.DefaultOptions(dbPath))
	if err != nil {
		checkError(err)
	}
	defer db.Close()

	// Initialize with the current set
	setsInPools[currentSet] = 1

	// Grab all of the pools in the google sheet
	var allPools = getPoolsFromSheet(leagueSheetID, poolLinkRange, googleApiSecretFile) //[0:1]

	// Fetch all the card data for the pools, and populate it into the supplied pool objects
	populatePools(db, allPools)

	// Filter the living from the dead
	alivePools := make([]PlayerPool, 0)
	deadPools := make([]PlayerPool, 0)
	for _, p := range allPools {
		if p.isAlive {
			alivePools = append(alivePools, p)
		} else {
			deadPools = append(deadPools, p)
		}
	}
	fmt.Printf("\n\nFound %d living pools and %d dead pools....\n", len(alivePools), len(deadPools))

	// Now dump stats for the pools
	fmt.Println("Analyzing living pools...")
	processPools(db, alivePools, "alive")

	fmt.Println("Analyzing dead pools...")
	processPools(db, deadPools, "dead")

	// And finally, do some "fun" analysis
	loadFunFactLists(db)
	processFunFacts(db, allPools)

	// Oh, and for bonus points dump out the day's performance data for the current set
	//dumpPerfromanceData(db, currentSet)
}

// Open the Google sheet and scrape out the list of pool links from the specific range they live in.
func getPoolsFromSheet(sheetID, sheetRange, secretFileName string) []PlayerPool {
	fmt.Println("Processing Sheet: ", sheetID)

	// Open the json secret file that we'll use for auth
	fmt.Println("Opening secrets file....")
	data, err := ioutil.ReadFile(secretFileName)
	checkError(err)
	conf, err := google.JWTConfigFromJSON(data, sheets.SpreadsheetsScope)
	checkError(err)

	// Make a Google Sheets client
	fmt.Println("Connecting to Google Sheets....")
	client := conf.Client(context.TODO())
	srv, err := sheets.New(client)
	checkError(err)

	// Read the column with the pool links
	fmt.Println("Opening sheet....")
	resp, err := srv.Spreadsheets.Values.Get(sheetID, sheetRange).Do()
	checkError(err)

	pools := make([]PlayerPool, 0)
	if len(resp.Values) == 0 {
		fmt.Println("No data found.")
	} else {
		for _, row := range resp.Values {
			playerName := fmt.Sprintf("%v", row[sheetPlayerColumnIndex])
			poolUri := fmt.Sprintf("%v", row[sheetLinkColumnIndex])
			losses, converr := strconv.Atoi(fmt.Sprintf("%v", row[sheetLossColumnIndex]))
			checkError(converr)
			wins, converr := strconv.Atoi(fmt.Sprintf("%v", row[sheetWinColumnIndex]))
			checkError(converr)

			pools = append(pools, makePool(playerName, "", poolUri, wins, losses))
		}
	}

	return pools
}

func populatePools(db *badger.DB, pools []PlayerPool) {
	// If the list of pools is empty, bail out
	if len(pools) == 0 {
		return
	}

	// For each pool, get the card list
	for i, pool := range pools {
		// Call the SealedDeck API and get back the deck
		var deck = getCardsFromPool(pool.player, pool.uri)
		pools[i].fetchCardData(db, deck)
	}
}

// Connect to SealedDeck.tech and grab the card list for a given pool
func getCardsFromPool(name string, uri string) *SealedDeck {
	fmt.Printf("Fetching pool for %s from: %s\n", name, uri)
	rawJson, err := getWebResponseString(uri)
	checkError(err)

	// Convert the json to our deck struct
	sealedDeck := new(SealedDeck)
	json.Unmarshal([]byte(rawJson), &sealedDeck)

	// take a nap to not hammer the site
	time.Sleep(sealedDeckPauseMs * time.Millisecond)

	return sealedDeck
}

// For a given deck, get a flattened and enriched set of card data and shove it into the supplied slice
func (pool *PlayerPool) fetchCardData(db *badger.DB, deck *SealedDeck) {

	// Flatten the deck into a series of cards
	allCards := deck.flatten()

	// Now populate the card data from the database (if we've seen it before) or scryfall
	for _, card := range allCards {
		resultCard, err := getCard(db, card.cardName)
		checkError(err)
		pool.cards = append(pool.cards, DeckSlot{amount: card.amount, cardName: card.cardName, card: resultCard})

		if !leagueIsMonoSet {
			setsInPools[strings.ToUpper(resultCard.Set)] = 1
		}
	}
}

// For a batch of pools, gather all the card data and dump it to a file.
func processPools(db *badger.DB, pools []PlayerPool, poolType string) {

	// If the list of pools is empty, bail out
	if len(pools) == 0 {
		return
	}

	// Make a master list of all of the cards across the set of pools
	allCards := make(map[string]DeckSlot)
	for _, pool := range pools {
		// Append the cards from the pool to the master list
		flattenDeckSlots(allCards, pool.cards)
	}

	// Write out a tab-delimited file for easy analysis
	outputFileName := fmt.Sprintf("%s\\ASL_%d_%d_%d_%d_%d_%s.txt", outputPath, time.Now().Year(), time.Now().Month(), time.Now().Day(), time.Now().Hour(), time.Now().Minute(), poolType)
	outputFile, err := os.Create(outputFileName)
	checkError(err)
	writer := bufio.NewWriter(outputFile)

	writer.WriteString("Name	Set	Rarity	ManaCost	TypeLine	PriceUSD	Amount\n")
	for _, ds := range allCards {
		theCard := ds.card
		writer.WriteString(fmt.Sprintf("%s	%s	%s	%s	%s	%s	%d\n", theCard.Name, theCard.Set, theCard.Rarity, theCard.getManaCost(), theCard.getTypeLineClean(), theCard.Prices.Usd, ds.amount))
	}
	writer.Flush()
}

// Place all cards into allCards.
// Rules:
// 1. If we haven't seen the card before, make a new entry for it
// 2. If we have seen the card before, add the copies to the existing entry
func (deck *SealedDeck) flatten() map[string]DeckSlot {
	// Append the deck & sideboard into one list
	var allCards = append(deck.Deck, deck.Sideboard...)

	// Add all cards from the main deck
	flattenedCards := make(map[string]DeckSlot)
	for _, card := range allCards {
		value, ok := flattenedCards[card.Name]
		if ok {
			flattenedCards[card.Name] = DeckSlot{amount: value.amount + card.Count, cardName: card.Name}
		} else {
			flattenedCards[card.Name] = DeckSlot{amount: card.Count, cardName: card.Name}
		}
	}

	return flattenedCards
}

// Place all cards into allCards.
// Rules:
// 1. If we haven't seen the card before, make a new entry for it
// 2. If we have seen the card before, add the copies to the existing entry
func flattenDeckSlots(allCards map[string]DeckSlot, cards []DeckSlot) {
	// Add all cards from the main deck
	for _, c := range cards {
		value, ok := allCards[c.cardName]
		if ok {
			allCards[c.cardName] = DeckSlot{amount: value.amount + c.amount, cardName: c.cardName, card: c.card}
		} else {
			allCards[c.cardName] = DeckSlot{amount: c.amount, cardName: c.cardName, card: c.card}
		}
	}
}

// Get the call from the database, or if it's not already there, pull it from scryfall instead.
// Note: be a good citizen to scryfall, and pause after getting the card
func getCard(db *badger.DB, cardName string) (resultCard *ScryfallCard, err error) { // TODO: Add the card type to the return value

	cardJson := ""
	card := new(ScryfallCard)

	// Remove the Alchemy designation from cards
	if strings.HasPrefix(cardName, "A-") {
		cardName = strings.Trim(cardName, "A-")
	}

	// First try to get the card from the database
	cardJson, err = dbGet(db, cardName)
	if err != nil {
		// If the db lookup failed, try to get the card from scryfall
		cardJson, err = scryfallGet(cardName)
		if err != nil {
			return card, errors.New(fmt.Sprintf("Could not find card in db or in scryfall: %s", cardName))
		}

		// Store it in the database for next time
		err = dbSet(db, cardName, cardJson)
		checkError(err)
	}

	// Return the card
	json.Unmarshal([]byte(cardJson), &card)
	return card, nil
}

func scryfallGet(cardName string) (resultJson string, err error) {
	fmt.Println("Fetching card from Scryfall: ", cardName)

	// We have a baseUri which fetches the card from whichever set scryfall fancies, and then a setUri that gets the card from the current set.
	// We want to try the current set to get the specifics for a card, and if that fails, fallback to the base uri.
	var baseUri string = fmt.Sprintf(scryfallCardTemplate, url.QueryEscape(cardName))
	var setUri string = baseUri + fmt.Sprintf(scryfallSetClauseTemplate, url.QueryEscape(currentSet))

	var rawJson string = ""
	rawJson, err = getWebResponseString(setUri)
	if err != nil {
		rawJson, err = getWebResponseString(baseUri)
	} else {
		fmt.Println(err)
	}

	// And then wait for a few ms to be a good citizen
	time.Sleep(scryfallPauseMs * time.Millisecond)

	return rawJson, err
}

// Load all deck card performance data for all decks
func loadCardPerformanceData(db *badger.DB) map[string]map[string]float64 {

	var cpByDeck = make(map[string]map[string]float64)

	// Walk the sets in order, and process the ones that we detect cards for
	for _, setCode := range allSeventeenLandsSets {
		if setsInPools[setCode] == 1 {
			fmt.Println("Fetching card performance data for ", setCode)

			// Grab 17lands perf data for this set
			// Note: If a specific card is in multiple sets, we grab the latest
			for _, deckId := range getDecks(setCode) {
				cp, err := getCardPerformanceData(db, setCode, deckId, false)
				
				// Shoot - we couldn't get perf data for this card.  Skip it for now?
				if err != nil {
					continue
				}

				// Extract the GIH_WR
				var gihByCard = make(map[string]float64)
				for _, cardData := range cp {
					if cardData.EverDrawnGameCount > getCardPrevalenceThreshold(cardData.Rarity) {
						gihByCard[cardData.Name] = cardData.EverDrawnWinRate
					} else { // filter out rarely played cards
						gihByCard[cardData.Name] = 0
					}
				}

				cpByDeck[deckId] = gihByCard
			} // end for
		} // end if
	} // end for

	return cpByDeck
}

// Get the call from the database, or if it's not already there, pull it from 17lands.com instead.
func getCardPerformanceData(db *badger.DB, setCode string, deckId string, forceDataRefresh bool) (resultCard CardPerformance, err error) {
	rawJson := ""
	cp := new(CardPerformance)

	// Build the key to access the set perf data.  If the set is the current one we'll refresh daily.  Otherwise, we rely on cached data
	var dateKey = ""
	if setCode == currentSet {
		dateKey = fmt.Sprintf("_%d_%d_%d", time.Now().Year(), time.Now().Month(), time.Now().Day())
	}
	var dbKey = fmt.Sprintf("17lands_%s_%s%s", setCode, deckId, dateKey)

	// Try to get the card from the database
	rawJson, err = dbGet(db, dbKey)
	if err != nil || strings.TrimSpace(rawJson) == "" || forceDataRefresh {
		// If the db lookup failed, try to get the data from 17lands
		rawJson, err = seventeenLandsGet(setCode, deckId)
		if err != nil {
			return *cp, errors.New(fmt.Sprintf("Could not find card perf data in db or on 17lands.com: %s", deckId))
		}

		// Store it in the database for next time
		err = dbSet(db, dbKey, rawJson)
		checkError(err)
	}

	// Return the card
	json.Unmarshal([]byte(rawJson), &cp)
	return *cp, nil
}

func seventeenLandsGet(setCode string, deckId string) (resultJson string, err error) {
	fmt.Println("Fetching card performance data from 17lands.com: ", deckId)

	//"https://www.17lands.com/card_ratings/data?expansion=%s&format=PremierDraft&start_date=%s&end_date%s&colors=%s"
	var todayString = fmt.Sprintf("%d-%d-%d", time.Now().Year(), time.Now().Month(), time.Now().Day())
	var uri string = fmt.Sprintf(seventeenLandsTemplate, setCode, setPerformanceFormat, todayString, deckId)
	//var uri string = fmt.Sprintf(seventeenLandsTemplate, setCode, deckId)
	rawJson, err := getWebResponseString(uri)
	if err != nil {
		fmt.Println(err)
	}

	// And then wait for a few ms to be a good citizen
	time.Sleep(seventeenLandsPauseMs * time.Millisecond)

	return rawJson, err
}

// A dumb little function that looks for a bunch of neato stats
func processFunFacts(db *badger.DB, pools []PlayerPool) {

	// Load up data about how the cards perform
	cardStrengthByDeck := loadCardPerformanceData(db) // TODO: all the sets that we care about....

	// We're going to zip through all of the pools, and add facts about each to them
	for i := range pools {
		pools[i].addFacts(cardStrengthByDeck)
	}

	// Write out a csv with all of the facts
	outputFileName := fmt.Sprintf("%s\\ASL_%d_%d_%d_%d_%d_funfacts.csv", outputPath, time.Now().Year(), time.Now().Month(), time.Now().Day(), time.Now().Hour(), time.Now().Minute())
	outputFile, err := os.Create(outputFileName)
	checkError(err)
	writer := bufio.NewWriter(outputFile)

	writer.WriteString("Player,Team,IsAlive,Record,Bombs,Duds,TopCommons,W,U,B,R,G,Gold,Colourless,Cmc,NonBasicLand,Commanders,Playsets,UniqueCards,CostUSD,Strength\n")
	for _, p := range pools {
		ff := p.facts
		writer.WriteString(fmt.Sprintf("%s,%s,%t,%s,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d\n",
			p.player, p.team, p.isAlive, p.record, ff["bombs"], ff["duds"], ff["topcommons"], ff["white"], ff["blue"], ff["black"], ff["red"], ff["green"], ff["gold"], ff["colourless"],
			ff["cmc"], ff["nonbasicland"], ff["commanders"], ff["playsets"], ff["uniqueCards"], ff["costUSD"], ff["strength"]))
	}
	writer.Flush()
}

func loadFunFactLists(db *badger.DB) {
	// Bombs (>= 63% WR)
	bombList = getCardsFromPool("Bombs", bombSealedDeckId).flatten()

	// Duds (<= 53% WR)
	dudList = getCardsFromPool("Duds", dudSealedDeckId).flatten()

	// Top Commons
	topCommonList = getCardsFromPool("TopCommons", topCommonDeckId).flatten()
}

func (pool *PlayerPool) addFacts(cardStrengthByDeck map[string]map[string]float64) {

	// Always fun
	var bombs = 0
	var duds = 0
	var topCommons = 0
	var whiteCard = 0
	var blueCard = 0
	var blackCard = 0
	var redCard = 0
	var greenCard = 0
	var goldCard = 0
	var colourless = 0
	var nonBasicLand = 0
	var playsets = 0
	var strength = 0
	var cmc = 0.0
	var costUSD = 0.0
	var uniqueCards = 0

	// League-specific
	var commanders = 0

	// Drop the basic lands (and command towers) and gather facts about the cards in the pool.
	for _, card := range pool.cards {
		// Filter out the basic lands
		if !card.isBasicLand() {

			// We're working with a de-dup'd list, so increment here.
			uniqueCards += 1

			// Bombs
			if isInCuratedSet(card.cardName, bombList) {
				bombs += card.amount
			}

			// Duds
			if isInCuratedSet(card.cardName, dudList) {
				duds += card.amount
			}

			// Top Commons
			if isInCuratedSet(card.cardName, topCommonList) {
				topCommons += card.amount
			}

			// Cards of each colour
			if card.isColour("W", true) {
				whiteCard += card.amount
			}
			if card.isColour("U", true) {
				blueCard += card.amount
			}
			if card.isColour("B", true) {
				blackCard += card.amount
			}
			if card.isColour("R", true) {
				redCard += card.amount
			}
			if card.isColour("G", true) {
				greenCard += card.amount
			}
			if card.isMultiColour() {
				goldCard += card.amount
			}
			if card.isColourless() && !card.isCardType("Land") {
				colourless += card.amount
			}

			// Non-basics
			if card.isCardType("Land") && !card.isBasicLand() {
				nonBasicLand += card.amount
			}

			// A playset (or more) of a card
			if card.amount >= 4 {
				playsets += 1
			}

			// $$$$
			cardCost, _ := strconv.ParseFloat(card.card.Prices.Usd, 64)
			costUSD += float64(card.amount) * cardCost

			// Total mana value of the pool
			cmc += float64(card.amount) * card.card.Cmc

			// Commanders are legendary creatures
			if card.isCardType("Legendary Creature") {
				commanders += 1 // card.amount  (don't count multiples)
			}

		}
	}

	// Now try to determine the deck strength
	strength = pool.calculateStrength(cardStrengthByDeck)

	// Add all the facts to the pool
	pool.facts["bombs"] = bombs
	pool.facts["duds"] = duds
	pool.facts["topcommons"] = topCommons
	pool.facts["white"] = whiteCard
	pool.facts["blue"] = blueCard
	pool.facts["black"] = blackCard
	pool.facts["red"] = redCard
	pool.facts["green"] = greenCard
	pool.facts["gold"] = goldCard
	pool.facts["colourless"] = colourless
	pool.facts["cmc"] = int(math.Round(cmc))
	pool.facts["nonbasicland"] = nonBasicLand
	pool.facts["commanders"] = commanders
	pool.facts["playsets"] = playsets
	pool.facts["uniqueCards"] = uniqueCards
	pool.facts["costUSD"] = int(math.Round(costUSD))
	pool.facts["strength"] = 0
	if pool.isAlive {
		pool.facts["strength"] = strength
	}
}

// Algorithm for Strength:
// For each colour pair (deck):
//     Pick the top X GIH WR cards and sum their WRs
// Pick the top 3 colour pairs and return a weighted strength (100% of 1st, 80% of 2nd, 40% of 3rd)
func (pool *PlayerPool) calculateStrength(cardStrengthByDeck map[string]map[string]float64) int {
	var strength = 0.0
	var deckStrengths = make(map[string]float64)

	// Walk through the colour pairs
	for _, deckId := range getDecks(currentSet) {
		var strengthMap = cardStrengthByDeck[deckId]
		var deckStrength = 0.0

		// Add strength objects for all cards in the pool (break multiples into separate entries)
		var cardStrengths = make([]CardStrength, 0)
		for _, c := range pool.cards {
			strength, ok := strengthMap[c.cardName]
			// one entry per copy
			for i := 0; i < c.amount; i++ {
				if ok {
					cardStrengths = append(cardStrengths, CardStrength{c.cardName, strength})
				} else { // didn't find the card.... just give it a 0 (TODO: in the future maybe this triggers a 17lands load)
					cardStrengths = append(cardStrengths, CardStrength{c.cardName, 0})
				}
			}

		}

		// Now sort by strength
		sort.Slice(cardStrengths, func(i, j int) bool {
			return cardStrengths[i].strength > cardStrengths[j].strength
		})

		// Sum the top X results
		var maxIndex = deckStrengthCardsToConsider
		if len(cardStrengths) < deckStrengthCardsToConsider { // protect from weeird edge case of a tiny pool
			maxIndex = len(cardStrengths)
		}
		for _, cs := range cardStrengths[0:maxIndex] {
			deckStrength += cs.strength
		}
		deckStrengths[deckId] = deckStrength
	}

	// Take the average of the top 3 strongest decks
	v := make([]float64, len(deckStrengths))
	for _, val := range deckStrengths {
		v = append(v, val)
	}
	sort.Slice(v, func(i, j int) bool {
		return v[i] > v[j]
	})

	// Take 100% of the best deck, 80% of the second best deck, and 40% of the third best deck to get total strength of the pool
	strength = (v[0] + (v[1] * 0.8) + (v[2] * 0.4)) * 100.0

	return int(strength)
}

// Grab the valid decks (e.g. RB, UWG)  for the specified set
func getDecks(setCode string) []string {
	var mtgDecks = make([]string, 0)
	mtgDecks = append(mtgDecks, mtg2CDecks...)
	_, ok := seventeenLands3CSets[setCode]
	if ok {
		mtgDecks = append(mtgDecks, mtg3CDecks...)
	}
	return mtgDecks
}

// Is the card in a list of cards that we've curated for some analysis?
func isInCuratedSet(cardName string, curatedCardNames map[string]DeckSlot) bool {
	_, ok := curatedCardNames[cardName]
	return ok
}

// Is the card a basic land (or command tower, which sealeddeck.tech inserts sometimes)
func (ds *DeckSlot) isBasicLand() bool {
	return ds.card.Name == "Plains" || ds.card.Name == "Island" || ds.card.Name == "Swamp" || ds.card.Name == "Mountain" || ds.card.Name == "Forest" || ds.card.Name == "Command Tower"
}

// Is this card the given colour identity?
// If mono=true, match only on mono-coloured cards
func (ds *DeckSlot) isColour(colour string, mono bool) bool {

	if mono && len(ds.card.ColorIdentity) > 1 {
		return false
	}

	for _, c := range ds.card.ColorIdentity {
		if c == colour {
			return true
		}
	}
	return false
}

func (ds *DeckSlot) isMultiColour() bool {
	return len(ds.card.ColorIdentity) > 1 && !ds.isCardType("Land")
}

func (ds *DeckSlot) isColourless() bool {
	return len(ds.card.ColorIdentity) == 0
}

// Checks if the card has a specific (case sensitive) type
func (ds *DeckSlot) isCardType(typePhrase string) bool {
	return strings.Contains(ds.card.getTypeLineClean(), typePhrase)
}

// Handle grabbing the mana cost for a scryfall card.
//
// The complexity is that double-faced cards bury the value in the card faces.
func (card *ScryfallCard) getManaCost() string {

	// A normal card
	if len(card.ManaCost) > 0 {
		return card.ManaCost
	}

	// Maybe dual-faced?
	if len(card.CardFaces) > 0 {
		if len(card.CardFaces[0].ManaCost) > 0 {
			return card.CardFaces[0].ManaCost
		}
		if len(card.CardFaces[1].ManaCost) > 0 {
			return card.CardFaces[1].ManaCost
		}
	}

	// Well, we tried
	return ""
}

func getCardPrevalenceThreshold(rarity string) int {
	if rarity == "uncommon" {
		return seventeenLandsDrawnThreshold / 2
	}
	if rarity == "rare" {
		return seventeenLandsDrawnThreshold / 4
	}
	if rarity == "mythic" {
		return seventeenLandsDrawnThreshold / 6
	}
	// common
	return seventeenLandsDrawnThreshold
}

// Eliminate the funky dash from the type line
func (card *ScryfallCard) getTypeLineClean() string {
	return strings.Replace(card.TypeLine, "—", "-", -1)
}

func dumpPerfromanceData(db *badger.DB, currentSet string) {

	// Open the output file
	outputFileName := fmt.Sprintf("%s\\%s_%d_%d_%d_%d_%d.csv", perfOutputPath, currentSet, time.Now().Year(), time.Now().Month(), time.Now().Day(), time.Now().Hour(), time.Now().Minute())
	outputFile, err := os.Create(outputFileName)
	checkError(err)
	writer := bufio.NewWriter(outputFile)

	writer.WriteString("Card,URL,Rarity,Colour,Deck,GIH WR\n")

	// Grab 17lands perf data for the set
	for _, deckId := range getDecks(currentSet) {
		cp, err := getCardPerformanceData(db, currentSet, deckId, debugging17Lands)
		checkError(err)

		// Extract the GIH_WR for each card and dump to file
		for _, cardData := range cp {
			var gihWR = 0.0
			if cardData.EverDrawnGameCount > getCardPrevalenceThreshold(cardData.Rarity) { // filter out rarely played cards
				gihWR = cardData.EverDrawnWinRate
			}
			var colour = "gold"           // default to gold since cards with more than one colour are listed as WUG, etc.
			if len(cardData.Color) == 0 { // an empty string signifies no colour
				colour = "colourless"
			}
			if len(cardData.Color) == 1 { // Exactly one character is W,U,B,R, or G
				colour = cardData.Color
			}
			writer.WriteString(fmt.Sprintf("%s,%s,%s,%s,%s,%.1f\n", strings.Replace(cardData.Name, ",", " ", -1), cardData.URL, cardData.Rarity, colour, deckId, gihWR*100))
		}
	}

	writer.Flush()
}

/*
 *
 * Helper methods start here!
 *
 */

// Constructor for a pool, because I suck at golang
func makePool(player string, team string, uri string, wins int, losses int) PlayerPool {
	// Pool is alive if losses is still within the threshold
	isAlive := losses < leagueEliminationLosses

	// Rip the suffix from a pool link, and add it to the API call
	poolLink := uri
	var lastSlash = strings.LastIndex(poolLink, "/")
	var poolId = poolLink[lastSlash+1:]
	var poolUri string = fmt.Sprintf(sealedDeckApiUriTemplate, poolId)
	var record string = fmt.Sprintf("%d | %d", wins, losses)

	return PlayerPool{player: player, team: team, uri: poolUri, isAlive: isAlive, record: record, facts: make(map[string]int)}
}

// Grab a json blob from the specific database for the given key, or nil if there is no value at that key
func dbGet(db *badger.DB, key string) (resultJson string, err error) {
	// Get the single card from the database
	err = db.View(func(txn *badger.Txn) error {
		item, err := txn.Get([]byte(key))
		if err != nil {
			return err
		}

		var valCopy []byte
		err = item.Value(func(val []byte) error {
			// This func with val would only be called if item.Value encounters no error.
			valCopy = append([]byte{}, val...)
			return nil
		})
		if err != nil {
			return err
		}

		// Must copy it to use it outside item.Value(...).
		resultJson = fmt.Sprintf("%s", valCopy)
		return nil
	})

	return resultJson, err
}

// Set a string value into a key in the database.
func dbSet(db *badger.DB, key, value string) error {
	err := db.Update(func(txn *badger.Txn) error {
		return txn.Set([]byte(key), []byte(value))
	})

	if err != nil {
		fmt.Printf("Failed to set key %s: %v\n", key, err)
		return err
	}

	return nil
}

// Helper method that takes a Uri and spits out the response as a string
// Retries a few times if an error is hit
func getWebResponseString(uri string) (rawResult string, err error) {

	// Try to hit the uri, and retry if an error code comes back.
	for i := 0; i < webRetires; i++ {
		var r string = ""
		r, err = innerGetWebResponseString(uri)
		if err == nil {
			return r, err
		}

		// Something happened - take a nap, and then iterate
		time.Sleep(webRetryMs * time.Millisecond)
	}

	// If we got this far we were unsuccessful.  Return the final error
	return "", err
}

// Helper method that takes a Uri and spits out the response as a string
func innerGetWebResponseString(uri string) (rawResult string, err error) {
	resp, err := http.Get(uri)
	checkError(err)

	if resp.StatusCode != 200 {
		err = errors.New(fmt.Sprintf("An error with code %d was throw trying to get a response from: %s", resp.StatusCode, uri))
		return "", err
	}

	body, err := ioutil.ReadAll(resp.Body)
	checkError(err)

	return string(body), err
}

// Dumb little function to make error handling easier.
func checkError(err error) {
	if err != nil {
		panic(err.Error())
	}
}

/*
 *
 * Auto-generated json-based structures start here
 *
 * See: https://mholt.github.io/json-to-go/
 *
 */

// Autogenerated sealeddeck.tech struct.
type SealedDeck struct {
	PoolID    string `json:"poolId"`
	Sideboard []struct {
		Name  string `json:"name"`
		Count int    `json:"count"`
	} `json:"sideboard"`
	Deck []struct {
		Name  string `json:"name"`
		Count int    `json:"count"`
	} `json:"deck"`
}

// Autogenerated scryfall struct.
type ScryfallCard struct {
	Object        string `json:"object"`
	ID            string `json:"id"`
	OracleID      string `json:"oracle_id"`
	MultiverseIds []int  `json:"multiverse_ids"`
	MtgoID        int    `json:"mtgo_id"`
	TcgplayerID   int    `json:"tcgplayer_id"`
	CardmarketID  int    `json:"cardmarket_id"`
	Name          string `json:"name"`
	Lang          string `json:"lang"`
	ReleasedAt    string `json:"released_at"`
	URI           string `json:"uri"`
	ScryfallURI   string `json:"scryfall_uri"`
	Layout        string `json:"layout"`
	HighresImage  bool   `json:"highres_image"`
	ImageStatus   string `json:"image_status"`
	ImageUris     struct {
		Small      string `json:"small"`
		Normal     string `json:"normal"`
		Large      string `json:"large"`
		Png        string `json:"png"`
		ArtCrop    string `json:"art_crop"`
		BorderCrop string `json:"border_crop"`
	} `json:"image_uris"`
	ManaCost      string        `json:"mana_cost"`
	Cmc           float64       `json:"cmc"`
	TypeLine      string        `json:"type_line"`
	OracleText    string        `json:"oracle_text"`
	Colors        []string      `json:"colors"`
	ColorIdentity []string      `json:"color_identity"`
	Keywords      []interface{} `json:"keywords"`
	CardFaces     []struct {
		Object         string   `json:"object"`
		Name           string   `json:"name"`
		ManaCost       string   `json:"mana_cost"`
		TypeLine       string   `json:"type_line"`
		OracleText     string   `json:"oracle_text"`
		Colors         []string `json:"colors"`
		Artist         string   `json:"artist"`
		ArtistID       string   `json:"artist_id"`
		IllustrationID string   `json:"illustration_id"`
		ImageUris      struct {
			Small      string `json:"small"`
			Normal     string `json:"normal"`
			Large      string `json:"large"`
			Png        string `json:"png"`
			ArtCrop    string `json:"art_crop"`
			BorderCrop string `json:"border_crop"`
		} `json:"image_uris"`
		FlavorName     string   `json:"flavor_name,omitempty"`
		ColorIndicator []string `json:"color_indicator,omitempty"`
		Power          string   `json:"power,omitempty"`
		Toughness      string   `json:"toughness,omitempty"`
		FlavorText     string   `json:"flavor_text,omitempty"`
	} `json:"card_faces"`
	Legalities struct {
		Standard        string `json:"standard"`
		Future          string `json:"future"`
		Historic        string `json:"historic"`
		Gladiator       string `json:"gladiator"`
		Pioneer         string `json:"pioneer"`
		Modern          string `json:"modern"`
		Legacy          string `json:"legacy"`
		Pauper          string `json:"pauper"`
		Vintage         string `json:"vintage"`
		Penny           string `json:"penny"`
		Commander       string `json:"commander"`
		Brawl           string `json:"brawl"`
		Historicbrawl   string `json:"historicbrawl"`
		Alchemy         string `json:"alchemy"`
		Paupercommander string `json:"paupercommander"`
		Duel            string `json:"duel"`
		Oldschool       string `json:"oldschool"`
		Premodern       string `json:"premodern"`
	} `json:"legalities"`
	Games           []string `json:"games"`
	Reserved        bool     `json:"reserved"`
	Foil            bool     `json:"foil"`
	Nonfoil         bool     `json:"nonfoil"`
	Finishes        []string `json:"finishes"`
	Oversized       bool     `json:"oversized"`
	Promo           bool     `json:"promo"`
	Reprint         bool     `json:"reprint"`
	Variation       bool     `json:"variation"`
	SetID           string   `json:"set_id"`
	Set             string   `json:"set"`
	SetName         string   `json:"set_name"`
	SetType         string   `json:"set_type"`
	SetURI          string   `json:"set_uri"`
	SetSearchURI    string   `json:"set_search_uri"`
	ScryfallSetURI  string   `json:"scryfall_set_uri"`
	RulingsURI      string   `json:"rulings_uri"`
	PrintsSearchURI string   `json:"prints_search_uri"`
	CollectorNumber string   `json:"collector_number"`
	Digital         bool     `json:"digital"`
	Rarity          string   `json:"rarity"`
	CardBackID      string   `json:"card_back_id"`
	Artist          string   `json:"artist"`
	ArtistIds       []string `json:"artist_ids"`
	IllustrationID  string   `json:"illustration_id"`
	BorderColor     string   `json:"border_color"`
	Frame           string   `json:"frame"`
	SecurityStamp   string   `json:"security_stamp"`
	FullArt         bool     `json:"full_art"`
	Textless        bool     `json:"textless"`
	Booster         bool     `json:"booster"`
	StorySpotlight  bool     `json:"story_spotlight"`
	EdhrecRank      int      `json:"edhrec_rank"`
	Preview         struct {
		Source      string `json:"source"`
		SourceURI   string `json:"source_uri"`
		PreviewedAt string `json:"previewed_at"`
	} `json:"preview"`
	Prices struct {
		Usd       string      `json:"usd"`
		UsdFoil   string      `json:"usd_foil"`
		UsdEtched interface{} `json:"usd_etched"`
		Eur       string      `json:"eur"`
		EurFoil   string      `json:"eur_foil"`
		Tix       string      `json:"tix"`
	} `json:"prices"`
	RelatedUris struct {
		Gatherer                  string `json:"gatherer"`
		TcgplayerInfiniteArticles string `json:"tcgplayer_infinite_articles"`
		TcgplayerInfiniteDecks    string `json:"tcgplayer_infinite_decks"`
		Edhrec                    string `json:"edhrec"`
		Mtgtop8                   string `json:"mtgtop8"`
	} `json:"related_uris"`
	PurchaseUris struct {
		Tcgplayer   string `json:"tcgplayer"`
		Cardmarket  string `json:"cardmarket"`
		Cardhoarder string `json:"cardhoarder"`
	} `json:"purchase_uris"`
}

// Autogenerated 17lands.com struct.
type CardPerformance []struct {
	SeenCount               int     `json:"seen_count"`
	AvgSeen                 float64 `json:"avg_seen"`
	PickCount               int     `json:"pick_count"`
	AvgPick                 float64 `json:"avg_pick"`
	GameCount               int     `json:"game_count"`
	WinRate                 float64 `json:"win_rate"`
	SideboardGameCount      int     `json:"sideboard_game_count"`
	SideboardWinRate        float64 `json:"sideboard_win_rate"`
	OpeningHandGameCount    int     `json:"opening_hand_game_count"`
	OpeningHandWinRate      float64 `json:"opening_hand_win_rate"`
	DrawnGameCount          int     `json:"drawn_game_count"`
	DrawnWinRate            float64 `json:"drawn_win_rate"`
	EverDrawnGameCount      int     `json:"ever_drawn_game_count"`
	EverDrawnWinRate        float64 `json:"ever_drawn_win_rate"`
	NeverDrawnGameCount     int     `json:"never_drawn_game_count"`
	NeverDrawnWinRate       float64 `json:"never_drawn_win_rate"`
	DrawnImprovementWinRate float64 `json:"drawn_improvement_win_rate"`
	Name                    string  `json:"name"`
	Color                   string  `json:"color"`
	Rarity                  string  `json:"rarity"`
	URL                     string  `json:"url"`
	URLBack                 string  `json:"url_back"`
}
