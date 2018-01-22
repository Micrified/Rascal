package nl.tudelft.jpacman.level;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import nl.tudelft.jpacman.board.Board;
import nl.tudelft.jpacman.board.Direction;
import nl.tudelft.jpacman.board.Square;
import nl.tudelft.jpacman.board.Unit;
import nl.tudelft.jpacman.npc.NPC;

@SuppressWarnings("PMD.TooManyMethods")
public class Level {
private final Board board;
private final Object moveLock = new Object();
private final Object startStopLock = new Object();
private final Map<NPC, ScheduledExecutorService> npcs;
private boolean inProgress;
private final List<Square> startSquares;
private int startSquareIndex;
private final List<Player> players;
private final CollisionMap collisions;
private final Set<LevelObserver> observers;
public Level(Board b, List<NPC> ghosts, List<Square> startPositions,
CollisionMap collisionMap) {
assert b != null;
assert ghosts != null;
assert startPositions != null;
this.board = b;
this.inProgress = false;
this.npcs = new HashMap<>();
for (NPC g : ghosts) {
npcs.put(g, null);
}
this.startSquares = startPositions;
this.startSquareIndex = 0;
this.players = new ArrayList<>();
this.collisions = collisionMap;
this.observers = new HashSet<>();
}
public void addObserver(LevelObserver observer) {
observers.add(observer);
}
public void removeObserver(LevelObserver observer) {
observers.remove(observer);
}
public void registerPlayer(Player p) {
assert p != null;
assert !startSquares.isEmpty();
if (players.contains(p)) {
return;
}
players.add(p);
Square square = startSquares.get(startSquareIndex);
p.occupy(square);
startSquareIndex++;
startSquareIndex %= startSquares.size();
}
public Board getBoard() {
return board;
}
public void move(Unit unit, Direction direction) {
assert unit != null;
assert direction != null;
if (!isInProgress()) {
return;
}
synchronized (moveLock) {
unit.setDirection(direction);
Square location = unit.getSquare();
Square destination = location.getSquareAt(direction);
if (destination.isAccessibleTo(unit)) {
List<Unit> occupants = destination.getOccupants();
unit.occupy(destination);
for (Unit occupant : occupants) {
collisions.collide(unit, occupant);
}
}
updateObservers();
}
}
public void start() {
synchronized (startStopLock) {
if (isInProgress()) {
return;
}
startNPCs();
inProgress = true;
updateObservers();
}
}
public void stop() {
synchronized (startStopLock) {
if (!isInProgress()) {
return;
}
stopNPCs();
inProgress = false;
}
}
private void startNPCs() {
for (final NPC npc : npcs.keySet()) {
ScheduledExecutorService service = Executors
.newSingleThreadScheduledExecutor();
service.schedule(new NpcMoveTask(service, npc),
npc.getInterval() / 2, TimeUnit.MILLISECONDS);
npcs.put(npc, service);
}
}
private void stopNPCs() {
for (Entry<NPC, ScheduledExecutorService> e : npcs.entrySet()) {
e.getValue().shutdownNow();
}
}
public boolean isInProgress() {
return inProgress;
}
private void updateObservers() {
if (!isAnyPlayerAlive()) {
for (LevelObserver o : observers) {
o.levelLost();
}
}
if (remainingPellets() == 0) {
for (LevelObserver o : observers) {
o.levelWon();
}
}
}
public boolean isAnyPlayerAlive() {
for (Player p : players) {
if (p.isAlive()) {
return true;
}
}
return false;
}
public int remainingPellets() {
Board b = getBoard();
int pellets = 0;
for (int x = 0; x < b.getWidth(); x++) {
for (int y = 0; y < b.getHeight(); y++) {
for (Unit u : b.squareAt(x, y).getOccupants()) {
if (u instanceof Pellet) {
pellets++;
}
}
}
}
assert pellets >= 0;
return pellets;
}
private final class NpcMoveTask implements Runnable {

private final ScheduledExecutorService service;

private final NPC npc;

NpcMoveTask(ScheduledExecutorService s, NPC n) {
this.service = s;
this.npc = n;
}
@Override
public void run() {
Direction nextMove = npc.nextMove();
if (nextMove != null) {
move(npc, nextMove);
}
long interval = npc.getInterval();
service.schedule(this, interval, TimeUnit.MILLISECONDS);
}
}
public interface LevelObserver {

void levelWon();

void levelLost();
}
}
