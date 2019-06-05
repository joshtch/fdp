import FDO from 'fdo';
import FDP from '../../src/fdp';

describe('fdp/dsl2ml.spec', () => {

  test('should only return results asked for', () => {
    expect(FDP.solve(`
      : A [0 0 2 2 5 5]
      : B [0 10]
      : C [0 1]
      A = B + C
      @custom targets(B)
    `, FDO.solve)).toEqual({B: 0}); // point is to only report var B, actual outcome irrelevant
  });
});
