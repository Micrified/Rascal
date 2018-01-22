packagenl.tudelft.jpacman.npc.ghost;

importstaticorg.junit.Assert.assertArrayEquals;
importstaticorg.junit.Assert.assertEquals;
importstaticorg.junit.Assert.assertNotNull;
importstaticorg.junit.Assert.assertNull;
importstaticorg.mockito.Mockito.mock;

importjava.io.IOException;
importjava.io.InputStream;
importjava.util.List;

importnl.tudelft.jpacman.board.Board;
importnl.tudelft.jpacman.board.BoardFactory;
importnl.tudelft.jpacman.board.Direction;
importnl.tudelft.jpacman.board.Square;
importnl.tudelft.jpacman.board.Unit;
importnl.tudelft.jpacman.level.LevelFactory;
importnl.tudelft.jpacman.level.MapParser;
importnl.tudelft.jpacman.level.Pellet;
importnl.tudelft.jpacman.sprite.PacManSprites;

importorg.junit.Before;
importorg.junit.Test;

importcom.google.common.collect.Lists;


@SuppressWarnings({"magicnumber","PMD.AvoidDuplicateLiterals","PMD.TooManyStaticImports""")).getBoard();
Squares1=b.squareAt(0,0);
Squares2=b.squareAt(0,0);
List<Direction>path=Navigation
.shortestPath(s1,s2,mock(Unit.class));
assertEquals(0,path.size());
}


@Test
publicvoidtestNoShortestPath(){
Boardb=parser
.parseMap(Lists.newArrayList("#####","###","#####"))
.getBoard();
Squares1=b.squareAt(1,1);
Squares2=b.squareAt(3,1);
List<Direction>path=Navigation
.shortestPath(s1,s2,mock(Unit.class));
assertNull(path);
}


@Test
publicvoidtestNoTraveller(){
Boardb=parser
.parseMap(Lists.newArrayList("#####","###","#####"))
.getBoard();
Squares1=b.squareAt(1,1);
Squares2=b.squareAt(3,1);
List<Direction>path=Navigation.shortestPath(s1,s2,null);
assertArrayEquals(newDirection[]{Direction.EAST,Direction.EAST},
path.toArray(newDirection[]{}));
}


@Test
publicvoidtestSimplePath(){
Boardb=parser.parseMap(Lists.newArrayList("####","##","####"))
.getBoard();
Squares1=b.squareAt(1,1);
Squares2=b.squareAt(2,1);
List<Direction>path=Navigation
.shortestPath(s1,s2,mock(Unit.class));
assertArrayEquals(newDirection[]{Direction.EAST},
path.toArray(newDirection[]{}));
}


@Test
publicvoidtestCornerPath(){
Boardb=parser.parseMap(
Lists.newArrayList("####","##","###","####")).getBoard();
Squares1=b.squareAt(1,1);
Squares2=b.squareAt(2,2);
List<Direction>path=Navigation
.shortestPath(s1,s2,mock(Unit.class));
assertArrayEquals(newDirection[]{Direction.EAST,Direction.SOUTH},
path.toArray(newDirection[]{}));
}


@Test
publicvoidtestNearestUnit(){
Boardb=parser
.parseMap(Lists.newArrayList("#####","#..#","#####""")).getBoard();
Squares1=b.squareAt(0,0);
Unitunit=Navigation.findNearest(Pellet.class,s1);
assertNull(unit);
}


@Test
publicvoidtestFullSizedLevel()throwsIOException{
try(InputStreami=getClass().getResourceAsStream("/board.txt")){
Boardb=parser.parseMap(i).getBoard();
Squares1=b.squareAt(1,1);
Unitunit=Navigation.findNearest(Ghost.class,s1);
assertNotNull(unit);
}
}
}
