package nl.tudelft.jpacman.game;
import java.util.List;
import nl.tudelft.jpacman.board.Direction;
import nl.tudelft.jpacman.level.Level;
import nl.tudelft.jpacman.level.Level.LevelObserver;
import nl.tudelft.jpacman.level.Player;

public abstract class Game implements LevelObserver {
private boolean inProgress;
private final Object progressLock = new Object();
protected Game() {
inProgress = false;
}
public void start() {
synchronized (progressLock) {
if (isInProgress()) {
return;
}
if (getLevel().isAnyPlayerAlive()
&& getLevel().remainingPellets() > 0) {
inProgress = true;
getLevel().addObserver(this);
getLevel().start();
}
}
}
public void stop() {
synchronized (progressLock) {
if (!isInProgress()) {
return;
}
inProgress = false;
getLevel().stop();
}
}
public boolean isInProgress() {
return inProgress;
}
public abstract List<Player> getPlayers();
public abstract Level getLevel();
public void move(Player player, Direction direction) {
if (isInProgress()) {
getLevel().move(player, direction);
}
}
@Override
public void levelWon() {
stop();
}
@Override
public void levelLost() {
stop();
}
}
